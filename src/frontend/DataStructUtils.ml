open Printing
open MiscUtils
open Pipeline.Tofino
open SetIR
open SetUtils
open DataStructIR
open Collections

let num_bit_api_call = 8

let num_bit_window_t = 16

let num_bit_clear_index = 1

let num_bit_reg_size_t = 32

(* Linked to "p"_value_t *)
(* Assumption: different hash crc polynomials for index and keys *)
let num_bit_timekey = 32

let max_bit_reg_ts = 16 (* 32 - 1 at max *)

let num_bit_signal = 1

let max_bit_index = 32

(* max_time_unit needs to be within the bound of ints due to Z.to_int usage
   and the bound of num_bit_window_t. *)
let max_time_unit = Z.( - ) (z_pow2 (num_bit_window_t - 1)) Z.one

let num_bit_prob = 16

let num_bit_pred = 4

let max_reg_entries = 2

let get_num_apis (api_set : api_set) =
  match api_set with
  | ASQ | ASI | ASInQ ->
      1
  | ASIQ | ASIInQ | ASQInQ ->
      2
  | ASIQInQ ->
      3

let get_num_reg_progs (api_set : api_set) (fold : bool) =
  if fold then
    match api_set with
    | ASQ ->
        1
    | ASI | ASInQ | ASIInQ ->
        2
    | ASIQ | ASQInQ ->
        3
    | ASIQInQ ->
        3
  else
    match api_set with
    | ASQ | ASI | ASInQ | ASIInQ ->
        1
    | ASIQ | ASQInQ ->
        2
    | ASIQInQ ->
        2

let get_time_lo (time : time_fun) =
  match time with TWithin (lo, hi) -> lo | TSince t -> t | TLast t -> t

let get_time_hi (time : time_fun) =
  match time with TWithin (lo, hi) -> hi | TSince t -> t | TLast t -> t

let get_block_slot_pairs (no_dup : bool) (num_bit_per_slot : int)
    (num_dist_keys : int) (max_block_per_reg : int) (num_bit_per_block : int) :
    (int * int) list =
  let max_num_slot_log2 =
    min max_bit_index
      (int_log2 (num_bit_per_block * max_block_per_reg / num_bit_per_slot))
  in
  let rec get_block_slot_pairs' (last_block : int) (i : int)
      (agg : (int * int) list) =
    if i = 1 then agg
    else
      let num_block =
        int_cdiv (num_bit_per_slot * int_pow2 i) num_bit_per_block
      in
      if num_block = last_block && no_dup then
        get_block_slot_pairs' num_block (i - 1) agg
      else (num_block, i) :: get_block_slot_pairs' num_block (i - 1) agg
  in
  if num_dist_keys = 0 then [(1, 0)]
  else get_block_slot_pairs' (-1) max_num_slot_log2 []

type crc_tup = int * bool * bool * bool * int * int

let gen_crc_polys (crc_num_bit : int) (tot_hash : int) :
    (crc_tup * (int * int) option) list =
  let crc_16 =
    [ (0x8005, true, false, false, 0x0000, 0x0000)
    ; (0x1021, false, false, false, 0xFFFF, 0x0000)
    ; (0x0589, false, false, false, 0x0001, 0x0001)
    ; (0x3D65, true, false, false, 0x0000, 0xFFFF)
    ; (0x8BB7, false, false, false, 0x0000, 0x0000)
    ; (0xA097, false, false, false, 0x0000, 0x0000)
    ; (0xC867, false, false, false, 0xFFFF, 0x0000) ]
  in
  let num_plain_crc_16 = List.length crc_16 in
  let crc_32 =
    [ (0x04C11DB7, true, false, false, 0x00000000, 0xFFFFFFFF)
    ; (0x1EDC6F41, true, false, false, 0x00000000, 0xFFFFFFFF)
    ; (0xA833982B, true, false, false, 0x00000000, 0xFFFFFFFF)
    ; (0x04C11DB7, false, false, false, 0xFFFFFFFF, 0x00000000)
    ; (0x814141AB, false, false, false, 0x00000000, 0x00000000)
    ; (0x000000AF, false, false, false, 0x00000000, 0x00000000) ]
  in
  let num_plain_crc_32 = List.length crc_32 in
  match crc_num_bit with
  | 8 ->
      [] (* Trivial *)
  | 16 ->
      let gen_salted_hash () =
        let poly_idx = Random.int (List.length crc_16) in
        (* Maximum input to Random.int: 2^30 *)
        let seed_width = min 30 (Random.int crc_num_bit + 1) in
        let seed_value = Random.int (int_pow2 seed_width - 1) in
        (List.nth crc_16 poly_idx, Some (seed_value, seed_width))
      in
      if tot_hash - num_plain_crc_16 > 0 then
        let extra_polys =
          map_for_range
            (fun _ -> gen_salted_hash ())
            1
            (tot_hash - num_plain_crc_16)
        in
        List.map (fun tup -> (tup, None)) crc_16 @ extra_polys
      else
        let plain_polys, _ = split_after_nth crc_16 (tot_hash - 1) in
        List.map (fun tup -> (tup, None)) plain_polys
  | 32 ->
      let gen_salted_hash () =
        let poly_idx = Random.int (List.length crc_32) in
        let seed_width = Random.int crc_num_bit in
        let seed_value = Random.int (int_pow2 seed_width - 1) in
        (List.nth crc_32 poly_idx, Some (seed_width, seed_value))
      in
      if tot_hash - num_plain_crc_32 > 0 then
        let extra_polys =
          map_for_range
            (fun _ -> gen_salted_hash ())
            1
            (tot_hash - num_plain_crc_32)
        in
        List.map (fun tup -> (tup, None)) crc_32 @ extra_polys
      else
        let plain_polys, _ = split_after_nth crc_32 (tot_hash - 1) in
        List.map (fun tup -> (tup, None)) plain_polys
  | _ ->
      raise (Error "[Bug] The number of bits in hash must be 8/16/32.")

let string_of_syninfo (syn : syninfo) =
  Printf.sprintf
    "{ set_name: %s; time_fun: [%s]; query_fun: [%s]; match_keys: [%s]; \
     branches: [%s]; api_set: %s }"
    syn.set_name
    (string_of_time syn.time_fun)
    (string_of_query syn.query_fun)
    (String.concat "," (List.map exp_to_string syn.match_keys))
    (String.concat "|" (List.map string_of_set_branch syn.branches))
    (string_of_api_set syn.api_set)

let print_syninfo_list (id_list : int list) (syn_list : syninfo list) =
  let _ =
    List.map2
      (fun id syn -> Printf.printf "\tNode %d: %s\n" id (string_of_syninfo syn))
      id_list syn_list
  in
  ()

let string_of_optinfo (opt : optinfo) =
  match opt with
  | OptBloom r_opt ->
      Printf.sprintf "Bloom { num_dist_keys: %d; num_api_calls: %d }"
        r_opt.num_dist_keys r_opt.num_apis
  | OptCMS r_opt ->
      Printf.sprintf "CMS { num_dist_keys: %d; num_api_calls: %d }"
        r_opt.num_dist_keys r_opt.num_apis
  | OptFold r_opt ->
      Printf.sprintf "Fold { num_dist_keys: %d; num_api_calls: %d }"
        r_opt.num_dist_keys r_opt.num_apis

let print_optinfo_list (opt_list : optinfo list) =
  let _ =
    List.map
      (fun syn -> Printf.printf "\t%s\n" (string_of_optinfo syn))
      opt_list
  in
  ()

let print_optinfo_choices (id_list : int list) (opt_choices : optinfo list list)
    =
  let _ =
    List.map2
      (fun id opt_list ->
        Printf.printf "Possible data structures for node %d:\n" id ;
        print_optinfo_list opt_list )
      id_list opt_choices
  in
  ()

let string_of_allocinfo (alloc : allocinfo) =
  match alloc with
  | AllocBloom r_alloc ->
      Printf.sprintf "Bloom { r: %d; w: %d; block: %d; num_slot_log2: %d }"
        r_alloc.r r_alloc.w r_alloc.block r_alloc.num_slot_log2
  | AllocCMS r_alloc ->
      Printf.sprintf "CMS { r: %d; w: %d; block: %d; num_slot_log2: %d }"
        r_alloc.r r_alloc.w r_alloc.block r_alloc.num_slot_log2
  | AllocFold r_alloc ->
      Printf.sprintf
        "Fold { r: %d; w: %d; block: %d; num_slot_log2: %d; num_32b_fp: %d }"
        r_alloc.r r_alloc.w r_alloc.block r_alloc.num_slot_log2
        r_alloc.num_32b_fp

let string_of_alloc_list (alloc_list : allocinfo list) =
  let result =
    List.fold_left
      (fun agg alloc -> agg ^ ", " ^ string_of_allocinfo alloc)
      "" alloc_list
  in
  match List.length alloc_list with
  | 0 ->
      result
  | _ ->
      String.sub result 2 (String.length result - 2)

let short_string_of_bool (b : bool) = if b then "T" else "F"

let string_of_nodetyp (nt : nodetyp) =
  match nt with
  | Clear (b1, b2) ->
      "Clear " ^ short_string_of_bool b1 ^ " " ^ short_string_of_bool b2
  | Hash b ->
      "Hash " ^ short_string_of_bool b
  | Table b ->
      "Table " ^ short_string_of_bool b
  | Atom b ->
      "Atom " ^ short_string_of_bool b
  | Reg b1 ->
      "Reg " ^ short_string_of_bool b1

let string_of_resnode (res : res_node) =
  Printf.sprintf
    "typ: %s\t{ num_tbl: %d; num_act: %d; num_hash: %d; num_reg: %d; \
     num_block: %d }"
    (string_of_nodetyp res.typ)
    res.num_tbl res.num_act res.num_hash res.num_reg res.num_block

let print_tu_map (tu_map : time_map) =
  Printf.printf "[Alloc] Time uitility map:\n" ;
  TimeMap.iter
    (fun (tframe, id, w) (num_unit, unit_len_log2, w_pure) ->
      Printf.printf "\t(%s, %d, %d) -> (%s, %d, %d)\n"
        (match tframe with Sliding -> "sliding" | Tumbling -> "tumbling")
        id w (Z.to_string num_unit) unit_len_log2 w_pure )
    tu_map

let print_au_list (au_list : (float * allocinfo list) list)
    (verbose : int option) =
  match verbose with
  | Some max_to_print ->
      if max_to_print < List.length au_list then (
        List.iter
          (fun (u, alloc_list) ->
            Printf.printf "\t%f, %s\n" u (string_of_alloc_list alloc_list) )
          (fst (split_after_nth au_list (max_to_print - 1))) ;
        Printf.printf "... %d configurations omitted ...\n"
          (List.length au_list - max_to_print) )
      else
        List.iter
          (fun (u, alloc_list) ->
            Printf.printf "\t%f, %s\n" u (string_of_alloc_list alloc_list) )
          au_list
  | None ->
      List.iter
        (fun (u, alloc_list) ->
          Printf.printf "\t%f, %s\n" u (string_of_alloc_list alloc_list) )
        au_list

let string_of_stage (res : stage_type) =
  Printf.sprintf
    "{ num_tbl: %d; num_act: %d; num_hash: %d; num_reg: %d; num_block: %d }"
    res.stage_table res.stage_action res.stage_hash res.stage_reg
    res.stage_block
