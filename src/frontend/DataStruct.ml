open Syntax
open SyntaxUtils
open MiscUtils
open Collections
open SetIR
open SetUtils
open DataStructIR
open DataStructUtils
open P4IR

(* Open Data Structure Modules*)
open Bloom
open Fold
open CountMinSketch

module Time = struct
  (* Handle both negative and positive time difference *)
  let get_time_diff (time : Z.t) (unit_len : Z.t) (num_unit : Z.t) (w_pure : Z.t)
      : Z.t =
    let win_len = Z.( * ) w_pure (Z.( * ) unit_len num_unit) in
    Z.abs (Z.( - ) win_len time)
end

let filter_opt_choices (ds_set : dstime_set) (id_list : int list)
    (syn_list : syninfo list) (opt_choices : optinfo list list) :
    optinfo list list =
  let filter_opt (id : int) (opt : optinfo) : optinfo option =
    let tframe =
      match opt with OptBloom _ | OptCMS _ -> Sliding | OptFold _ -> Tumbling
    in
    match DSMap.find_option ds_set (tframe, id) with
    | None ->
        None
    | _ ->
        Some opt
  in
  let filter_opt_list (id : int) (syn : syninfo) (opt_list : optinfo list) :
      optinfo list =
    let valid_opt_list = List.filter_map (filter_opt id) opt_list in
    if List.length valid_opt_list = 0 then
      raise
        (Error
           ( "[Alloc] The query " ^ string_of_int id
           ^ " has zero configuration for the temporal construct ["
           ^ string_of_time syn.time_fun
           ^ "]. Please consider loosening the error bound or lowering the \
              window size." ) ) ;
    valid_opt_list
  in
  list_map_3 filter_opt_list id_list syn_list opt_choices

let is_tumbling (time : time_fun) (tframe : tframe_ty) =
  match (time, tframe) with
  | TWithin _, _ ->
      None
  | TLast _, Sliding ->
      Some 3
  | TLast _, Tumbling ->
      Some 2
  | TSince _, Sliding ->
      Some 2
  | TSince _, Tumbling ->
      Some 1

(* Intentionally only a unique pair *)
let get_alloc (reg_bound : int) (syn : syninfo) (opt : optinfo) : allocinfo list
    =
  match opt with
  | OptBloom _ ->
      let reg_pairs =
        create_reg_pairs reg_bound (is_tumbling syn.time_fun Sliding)
      in
      Bloom.get_alloc reg_pairs
  | OptCMS _ ->
      let reg_pairs =
        create_reg_pairs reg_bound (is_tumbling syn.time_fun Sliding)
      in
      CMS.get_alloc reg_pairs
  | OptFold _ ->
      let reg_bound' = reg_bound / 2 in
      let reg_pairs =
        create_reg_pairs reg_bound' (is_tumbling syn.time_fun Tumbling)
      in
      Fold.get_alloc reg_pairs

let get_alloc_lists (reg_bound : int) (syn_list : syninfo list)
    (opt_list : optinfo list) : allocinfo list list =
  let alloc_list = list_map2 (get_alloc reg_bound) syn_list opt_list in
  cross_prod alloc_list

let calc_reg (alloc_list : allocinfo list) : int =
  let get_num_reg (alloc : allocinfo) =
    match alloc with
    | AllocBloom record ->
        record.w * record.r
    | AllocCMS record ->
        record.w * record.r
    | AllocFold record ->
        record.w * record.r * 2
  in
  List.fold_left ( + ) 0 (list_map get_num_reg alloc_list)

let quick_check_reg (max_reg : int) (alloc_lists : allocinfo list list) :
    allocinfo list list =
  let quick_check_reg' (alloc_list : allocinfo list) =
    calc_reg alloc_list <= max_reg
  in
  List.filter quick_check_reg' alloc_lists

let quick_check_block (max_block : int) (opt_list : optinfo list)
    (alloc_lists : allocinfo list list) : allocinfo list list =
  let quick_check_block' (alloc_list : allocinfo list) =
    let get_num_block (opt : optinfo) (alloc : allocinfo) =
      match (alloc, opt) with
      | AllocBloom r_alloc, OptBloom _ ->
          r_alloc.w * r_alloc.r * (r_alloc.block + 1)
      | AllocCMS r_alloc, OptCMS _ ->
          r_alloc.w * r_alloc.r * (r_alloc.block + 1)
      | AllocFold r_alloc, OptFold r_opt ->
          r_alloc.w * r_alloc.r
          * ( r_alloc.num_32b_fp
            + if r_alloc.timestamp then 1 else 0 + r_opt.num_entries )
          * (r_alloc.block + 1)
      | _, _ ->
          raise (Error "[Bug] Opt and Alloc do not match.")
    in
    let tot_block =
      List.fold_left ( + ) 0 (list_map2 get_num_block opt_list alloc_list)
    in
    if tot_block <= max_block then true else false
  in
  List.filter quick_check_block' alloc_lists

let add_num_block (max_block_per_reg : int) (max_block : int)
    (num_bit_per_block : int) (opt_list : optinfo list)
    (alloc_lists : allocinfo list list) : allocinfo list list =
  let get_bs_pairs (opt : optinfo) =
    match opt with
    | OptBloom record ->
        Bloom.get_block_slot_pairs record max_block_per_reg num_bit_per_block
    | OptCMS record ->
        CMS.get_block_slot_pairs record max_block_per_reg num_bit_per_block
    | OptFold record ->
        Fold.get_block_slot_pairs record max_block_per_reg num_bit_per_block
  in
  if List.length alloc_lists = 0 then alloc_lists
  else
    let bs_list = list_map get_bs_pairs opt_list in
    let add_num_block' (opt : optinfo) (alloc : allocinfo)
        (bs_pairs : (int * int) list) =
      match (alloc, opt) with
      | AllocBloom r_alloc, OptBloom r_opt ->
          Bloom.add_block bs_pairs r_opt r_alloc
      | AllocCMS r_alloc, OptCMS r_opt ->
          CMS.add_block bs_pairs r_opt r_alloc
      | AllocFold r_alloc, OptFold r_opt ->
          Fold.add_block bs_pairs r_opt r_alloc
      | _, _ ->
          raise (Error "[Bug] Opt and Alloc do not match.")
    in
    let add_num_block'' (alloc_list : allocinfo list) =
      let alloc_lists =
        cross_prod (list_map_3 add_num_block' opt_list alloc_list bs_list)
      in
      quick_check_block max_block opt_list alloc_lists
    in
    list_map add_num_block'' alloc_lists |> list_flatten

let filter_by_w (tu_map : time_map) (id : int) (time : time_fun)
    (alloc : allocinfo) : bool =
  let tframe, w =
    match alloc with
    | AllocBloom record | AllocCMS record ->
        (Sliding, record.w)
    | AllocFold record ->
        (Tumbling, record.w)
  in
  match TimeMap.find_option tu_map (tframe, id, w) with
  | None ->
      false
  | _ ->
      true

let dup_paired_param_ds (tu_map : time_map) (id_list : int list)
    (syn_list : syninfo list) (alloc_lists : allocinfo list list) =
  let dup_paired_param_ds' (id : int) (syn : syninfo) (alloc : allocinfo) =
    match alloc with
    | AllocBloom record ->
        let all_pairs =
          if record.r = record.w then [alloc]
          else [alloc; AllocBloom {record with w= record.r; r= record.w}]
        in
        List.filter (filter_by_w tu_map id syn.time_fun) all_pairs
    | AllocCMS record ->
        let all_pairs =
          if record.r = record.w then [alloc]
          else [alloc; AllocCMS {record with w= record.r; r= record.w}]
        in
        List.filter (filter_by_w tu_map id syn.time_fun) all_pairs
    | AllocFold record ->
        let all_pairs =
          if record.r = record.w then [alloc]
          else [alloc; AllocFold {record with w= record.r; r= record.w}]
        in
        List.filter (filter_by_w tu_map id syn.time_fun) all_pairs
  in
  let dup_paired_param_ds'' (alloc_list : allocinfo list) =
    cross_prod (list_map_3 dup_paired_param_ds' id_list syn_list alloc_list)
  in
  list_map dup_paired_param_ds'' alloc_lists |> list_flatten

(* loss * num_unit_per_w * unit_len_log2 *)

(* print tu_map;
   print_stage with LLOacation *)
(* Get time utility for sliding and tumbling window schemes *)
let get_time_utility (num_bit_in_ts : int) (max_reg : int) (id_list : int list)
    (syn_list : syninfo list) : time_map * dstime_set =
  let get_tu_within_sliding (time_lo : Z.t) (time_hi : Z.t) (w : Z.t)
      (unit_len_log2 : int) =
    let unit_len = z_pow2 unit_len_log2 in
    let w_pure_lo = Z.( - ) w (Z.of_int 2) in
    let w_pure_hi = Z.( - ) w Z.one in
    let num_unit = Z.cdiv time_lo (Z.( * ) unit_len w_pure_lo) in
    if
      Z.( * ) num_unit w > max_time_unit
      || Z.( * ) unit_len (Z.( * ) num_unit w_pure_hi) > time_hi
    then []
    else
      [ ( Time.get_time_diff time_lo unit_len num_unit w_pure_lo
        , num_unit
        , unit_len_log2
        , Z.to_int w_pure_hi ) ]
  in
  let get_tu_since_last_sliding (time_hi : Z.t) (w : Z.t) (unit_len_log2 : int)
      =
    let unit_len = z_pow2 unit_len_log2 in
    let w_pure_hi = Z.one in
    let get_tu_since_sliding' divfun =
      let num_unit = divfun time_hi (Z.( * ) unit_len w_pure_hi) in
      if Z.( * ) num_unit w > max_time_unit then [] else [num_unit]
    in
    let num_unit_list =
      list_map get_tu_since_sliding' [Z.fdiv; Z.cdiv] |> List.flatten
    in
    list_map
      (fun num_unit ->
        ( Time.get_time_diff time_hi unit_len num_unit w_pure_hi
        , num_unit
        , unit_len_log2
        , Z.to_int w_pure_hi ) )
      num_unit_list
  in
  let get_tu_within_tumbling (time_lo : Z.t) (time_hi : Z.t) (w : Z.t)
      (unit_len_log2 : int) =
    let unit_len = z_pow2 unit_len_log2 in
    let w_pure_lo = Z.( - ) w (Z.of_int 2) in
    let w_pure_hi = w in
    let num_unit = Z.cdiv time_lo (Z.( * ) unit_len w_pure_lo) in
    if
      Z.( * ) num_unit w > max_time_unit
      || Z.( * ) unit_len (Z.( * ) num_unit w_pure_hi) > time_hi
      (* Z.log2 (Z.( - ) time_hi Z.one) < num_bit_in_ts - 1 *)
      (* Past:
          unit_len_log2 + Z.log2up (Z.( + ) (Z.( * ) w num_unit) Z.one)
          < num_bit_in_ts - 1 *)
      || Z.log2 (Z.( - ) (Z.( * ) unit_len (Z.( * ) w num_unit)) Z.one)
         > num_bit_in_ts - 2
    then []
    else
      [ ( Time.get_time_diff time_lo unit_len num_unit w_pure_lo
        , num_unit
        , unit_len_log2
        , Z.to_int w_pure_hi ) ]
  in
  let get_tu_last_tumbling (time_hi : Z.t) (w : Z.t) (unit_len_log2 : int) =
    let unit_len = z_pow2 unit_len_log2 in
    let w_pure_hi = Z.one in
    let get_tu_since_sliding' divfun =
      let num_unit = divfun time_hi (Z.( * ) unit_len w_pure_hi) in
      if num_unit = Z.zero then []
      else if
        Z.( * ) num_unit w > max_time_unit
        || Z.log2 (Z.( - ) (Z.( * ) unit_len (Z.( * ) w num_unit)) Z.one)
           > num_bit_in_ts - 2
      then []
      else [num_unit]
    in
    let num_unit_list =
      list_map get_tu_since_sliding' [Z.fdiv; Z.cdiv] |> List.flatten
    in
    list_map
      (fun num_unit ->
        ( Time.get_time_diff time_hi unit_len num_unit w_pure_hi
        , num_unit
        , unit_len_log2
        , Z.to_int w_pure_hi ) )
      num_unit_list
  in
  let get_tu_for_w_1 (time_hi : Z.t) : (Z.t * int * int) option =
    let time_log2 = Z.log2 (Z.( - ) time_hi Z.one) in
    (* at least one clearing window *)
    (* does it fail? check *)
    if time_log2 > num_bit_in_ts - 2 then None
    else
      let num_bit_end = max max_bit_reg_ts (time_log2 + 1) in
      let time_shift =
        min (num_bit_in_ts - num_bit_timekey) (num_bit_end - max_bit_reg_ts)
      in
      let trunc_win_len_lo = Z.shift_right time_hi time_shift in
      let win_len_lo = Z.shift_left trunc_win_len_lo time_shift in
      let trunc_win_len_hi = Z.( + ) Z.one (Z.shift_right time_hi time_shift) in
      let win_len_hi = Z.shift_left trunc_win_len_hi time_shift in
      let trunc_win_len =
        if Z.gt (Z.( - ) time_hi win_len_lo) (Z.( - ) win_len_hi time_hi) then
          trunc_win_len_hi
        else trunc_win_len_lo
      in
      Some
        ( trunc_win_len (* saving something more meaningful in this case *)
        , num_bit_end - 1
        , 1 )
  in
  let get_tup_with_min_tu (gen_tu_tup_list : int -> (Z.t * Z.t * int * int) list)
      : (Z.t * int * int) option =
    let max_unit_len_log2 = num_bit_in_ts - 1 in
    let min_unit_len_log2 = 1 in
    let tu_list =
      map_for_range gen_tu_tup_list min_unit_len_log2 max_unit_len_log2
      |> List.flatten
    in
    if List.length tu_list = 0 then None
    else
      let get_tu (tu, _, _, _) = tu in
      let get_tup (_, num_unit, unit_len_log2, w_pure) =
        (num_unit, unit_len_log2, w_pure)
      in
      let max_tu =
        List.fold_left
          (fun agg tup -> if get_tu tup > agg then get_tu tup else agg)
          Z.zero tu_list
      in
      (* Favor large unit_len_log2 *)
      Some
        (get_tup
           (List.fold_right
              (fun agg tup -> if get_tu tup < get_tu agg then tup else agg)
              tu_list (max_tu, Z.zero, 0, 0) ) )
  in
  let get_tu_given_w (tframe : tframe_ty) (time : time_fun) (w : int) :
      (Z.t * int * int) option =
    let w = Z.of_int w in
    match (time, tframe) with
    | TWithin (lo, hi), Sliding ->
        get_tup_with_min_tu (get_tu_within_sliding lo hi w)
    | TLast t, Sliding ->
        get_tup_with_min_tu (get_tu_since_last_sliding t w)
    | TSince t, Sliding ->
        get_tup_with_min_tu (get_tu_since_last_sliding t w)
    | TWithin (lo, hi), Tumbling ->
        get_tup_with_min_tu (get_tu_within_tumbling lo hi w)
    | TSince t, Tumbling ->
        get_tu_for_w_1 t
    | TLast t, Tumbling ->
        get_tup_with_min_tu (get_tu_last_tumbling t w)
  in
  let get_tu_map_for_every_ds (agg1 : time_map) (agg2 : dstime_set)
      (tframe : tframe_ty) (id : int) (syn : syninfo) =
    let time =
      match syn.time_fun with
      | TWithin (lo, hi) ->
          if lo = Z.zero then TSince hi else syn.time_fun
      | _ ->
          syn.time_fun
    in
    let min_w, max_w =
      match (time, tframe) with
      | TWithin (lo, hi), Sliding ->
          (Z.to_int (Z.cdiv lo (Z.( - ) hi lo)) + 2, max_reg)
      | TSince _, Sliding ->
          (2, 2)
      | TLast _, Sliding ->
          (3, 3)
      | TWithin (lo, hi), Tumbling ->
          ( Z.to_int (Z.cdiv lo (Z.( / ) (Z.( - ) hi lo) (Z.of_int 2))) + 2
          , max_reg )
      | TSince _, Tumbling ->
          (1, 1)
      | TLast _, Tumbling ->
          (2, 2)
    in
    let tu_list =
      map_for_range
        (fun w ->
          match get_tu_given_w tframe time w with
          | None ->
              None
          | Some tu ->
              Some (w, tu) )
        min_w max_w
    in
    let tu_list_except_none = List.filter_map (fun elem -> elem) tu_list in
    if List.length tu_list_except_none != 0 then
      let _ =
        list_map
          (fun (w, tu) -> TimeMap.replace agg1 (tframe, id, w) tu)
          tu_list_except_none
      in
      DSMap.replace agg2 (tframe, id) ()
  in
  let tu_map = TimeMap.create (List.length syn_list * max_reg) in
  let ds_set = DSMap.create (List.length syn_list) in
  let _ =
    list_map2 (get_tu_map_for_every_ds tu_map ds_set Tumbling) id_list syn_list
  in
  let _ =
    list_map2 (get_tu_map_for_every_ds tu_map ds_set Sliding) id_list syn_list
  in
  (tu_map, ds_set)

let get_utility (num_bit_in_ts : int) (tu_map : time_map) (id_list : int list)
    (syn_list : syninfo list) (opt_list : optinfo list)
    (alloc_lists : allocinfo list list) (input_spec_map : input_map) =
  let get_utility_for_every_ds (tu_map : time_map) (id : int) (syn : syninfo)
      (opt : optinfo) (alloc : allocinfo) =
    match (alloc, opt) with
    | AllocBloom r_alloc, OptBloom r_opt ->
        let num_unit, unit_len_log2, w_pure =
          try TimeMap.find tu_map (Sliding, id, r_alloc.w)
          with Not_found -> raise (Error "[Bug] Time utility not in time_map.")
        in
        let time_hi =
          Z.( * ) (Z.of_int w_pure) (Z.( * ) num_unit (z_pow2 unit_len_log2))
        in
        Bloom.get_utility w_pure time_hi id syn r_opt r_alloc input_spec_map
    | AllocCMS r_alloc, OptCMS r_opt ->
        let num_unit, unit_len_log2, w_pure =
          try TimeMap.find tu_map (Sliding, id, r_alloc.w)
          with Not_found -> raise (Error "[Bug] Time utility not in time_map.")
        in
        let time_hi =
          Z.( * ) (Z.of_int w_pure) (Z.( * ) num_unit (z_pow2 unit_len_log2))
        in
        CMS.get_utility w_pure time_hi id syn r_opt r_alloc input_spec_map
    | AllocFold r_alloc, OptFold r_opt ->
        let lookup_w = if r_alloc.timestamp then r_alloc.w else r_alloc.w - 1 in
        let num_unit, unit_len_log2, w_pure =
          try TimeMap.find tu_map (Tumbling, id, lookup_w)
          with Not_found -> raise (Error "[Bug] Time utility not in time_map.")
        in
        let time_hi =
          if r_alloc.w = 1 then
            let time_shift =
              min
                (num_bit_in_ts - num_bit_timekey)
                (unit_len_log2 + 1 - max_bit_reg_ts)
            in
            Z.shift_left num_unit time_shift
          else
            Z.( * ) (Z.of_int w_pure) (Z.( * ) num_unit (z_pow2 unit_len_log2))
        in
        Fold.get_utility w_pure time_hi id syn r_opt r_alloc input_spec_map
    | _, _ ->
        raise (Error "[Bug] Opt and Alloc do not match.")
  in
  let get_utility_for_every_alloclist (alloc_list : allocinfo list) =
    let u_list =
      list_map_4
        (get_utility_for_every_ds tu_map)
        id_list syn_list opt_list alloc_list
    in
    let tot_u = List.fold_left F.add 0. u_list in
    (tot_u, alloc_list)
  in
  list_map get_utility_for_every_alloclist alloc_lists

let rec find_opt_choice (opt_list : optinfo list) (alloc : allocinfo) : optinfo
    =
  match opt_list with
  | hd :: tl -> (
    match (hd, alloc) with
    | OptBloom _, AllocBloom _ | OptCMS _, AllocCMS _ | OptFold _, AllocFold _
      ->
        hd
    | _, _ ->
        find_opt_choice tl alloc )
  | [] ->
      raise
        (Error
           "[Bug] Opt choice list does not contain the alloc data structure." )

let get_res_nodes (stage_hash : int) (stage_action : int)
    (max_hash_per_table : int) (min_bit_per_hash : int) (num_bit_in_ts : int)
    (max_idx_per_phv : int) (tu_map : time_map) (id : int) (atomize : bool)
    (syn : syninfo) (opt_list : optinfo list) (alloc : allocinfo) :
    res_node list =
  let opt = find_opt_choice opt_list alloc in
  match (alloc, opt) with
  | AllocBloom r_alloc, OptBloom r_opt ->
      let num_unit, unit_len_log2, _ =
        TimeMap.find tu_map (Sliding, id, r_alloc.w)
      in
      Bloom.get_res_nodes stage_hash stage_action max_hash_per_table
        min_bit_per_hash num_bit_in_ts max_idx_per_phv num_unit unit_len_log2
        atomize syn r_opt r_alloc
  | AllocCMS r_alloc, OptCMS r_opt ->
      let num_unit, unit_len_log2, _ =
        TimeMap.find tu_map (Sliding, id, r_alloc.w)
      in
      CMS.get_res_nodes stage_hash stage_action max_hash_per_table
        min_bit_per_hash num_bit_in_ts max_idx_per_phv num_unit unit_len_log2
        atomize syn r_opt r_alloc
  | AllocFold r_alloc, OptFold r_opt ->
      let lookup_w = if r_alloc.timestamp then r_alloc.w else r_alloc.w - 1 in
      let num_unit, unit_len_log2, _ =
        TimeMap.find tu_map (Tumbling, id, lookup_w)
      in
      Fold.get_res_nodes stage_hash stage_action max_hash_per_table
        min_bit_per_hash num_bit_in_ts max_idx_per_phv num_unit unit_len_log2
        atomize syn r_opt r_alloc
  | _, _ ->
      raise (Error "[Bug] Opt and Alloc do not match.")

let get_res_nodes_and_p4 (stage_hash : int) (stage_action : int)
    (max_hash_per_table : int) (min_bit_per_hash : int) (num_bit_in_ts : int)
    (max_idx_per_phv : int) (tu_map : time_map) (id : int) (var : Cid.t)
    (atomize : bool) (syn : syninfo) (opt_list : optinfo list)
    (alloc : allocinfo) : (res_node list * code_type) list =
  Random.self_init () ;
  let opt = find_opt_choice opt_list alloc in
  match (alloc, opt) with
  | AllocBloom r_alloc, OptBloom r_opt ->
      let num_unit, unit_len_log2, _ =
        TimeMap.find tu_map (Sliding, id, r_alloc.w)
      in
      let prefix = "bf" ^ string_of_int id ^ "_" in
      Bloom.get_res_nodes_and_p4 prefix stage_hash stage_action
        max_hash_per_table min_bit_per_hash num_bit_in_ts max_idx_per_phv
        num_unit unit_len_log2 var atomize syn r_opt r_alloc
  | AllocCMS r_alloc, OptCMS r_opt ->
      let num_unit, unit_len_log2, _ =
        TimeMap.find tu_map (Sliding, id, r_alloc.w)
      in
      let prefix = "cm" ^ string_of_int id ^ "_" in
      CMS.get_res_nodes_and_p4 prefix stage_hash stage_action max_hash_per_table
        min_bit_per_hash num_bit_in_ts max_idx_per_phv num_unit unit_len_log2
        var atomize syn r_opt r_alloc
  | AllocFold r_alloc, OptFold r_opt ->
      let lookup_w = if r_alloc.timestamp then r_alloc.w else r_alloc.w - 1 in
      let num_unit, unit_len_log2, _ =
        TimeMap.find tu_map (Tumbling, id, lookup_w)
      in
      let prefix = "fd" ^ string_of_int id ^ "_" in
      Fold.get_res_nodes_and_p4 prefix stage_hash stage_action
        max_hash_per_table min_bit_per_hash num_bit_in_ts max_idx_per_phv
        num_unit unit_len_log2 var atomize syn r_opt r_alloc
  | _, _ ->
      raise (Error "[Bug] Opt and Alloc do not match.")
