open SyntaxUtils
open MiscUtils
open Dataflow
open DataStructIR
open DataStructUtils
open DataStructShared
open SetIR
open P4IR
open SetUtils
open TransUtils
open Collections
module P4Alias = Poulet4.Syntax

module Fold :
  DS with type opt_rec = fold_opt_rec and type alloc_rec = fold_alloc_rec =
struct
  type opt_rec = fold_opt_rec

  type alloc_rec = fold_alloc_rec

  let num_bit_per_slot = 32

  let get_alloc (reg_pairs : (int * int) list) : allocinfo list =
    List.filter_map
      (fun (w, r) ->
        if w * r > 15 then None
        else
          Some
            (AllocFold
               {w; r; block= 0; num_slot_log2= 0; num_32b_fp= 1; timestamp= true}
            ) )
      reg_pairs

  let add_block (bs_list : (int * int) list) (opt : opt_rec) (alloc : alloc_rec)
      : allocinfo list =
    let add_block' (block, num_slot_log2) =
      let add_fp num_32b_fp =
        if alloc.w <= 2 then
          [ AllocFold
              {alloc with block; num_slot_log2; num_32b_fp; timestamp= true} ]
        else
          [ AllocFold
              {alloc with block; num_slot_log2; num_32b_fp; timestamp= true} ]
        (* ; AllocFold
           {alloc with block; num_slot_log2; num_32b_fp; timestamp= false} *)
      in
      let alloc_key_as_idx () =
        (* PEquality checkes ensures than alloc.r < opt.key_length *)
        if Z.of_int (alloc.r * int_pow2 num_slot_log2) = z_pow2 opt.key_length
        then add_fp 0
        else []
      in
      let num_32b_key = int_cdiv opt.key_length num_bit_timekey in
      match opt.err with
      | Exactset ->
          alloc_key_as_idx ()
      | Superset ->
          (* alloc_key_as_idx () @ something *)
          raise (Error "[Fold] Not implemented yet.")
      | Subset ->
          alloc_key_as_idx () @ add_fp num_32b_key
      | Approxset ->
          alloc_key_as_idx ()
          @ (map_for_range add_fp 1 num_32b_key |> List.flatten)
    in
    List.map add_block' bs_list |> List.flatten

  let get_block_slot_pairs (opt : opt_rec) : int -> int -> (int * int) list =
    match opt.err with
    | Exactset ->
        get_block_slot_pairs false num_bit_per_slot opt.num_dist_keys
    | _ ->
        get_block_slot_pairs true num_bit_per_slot opt.num_dist_keys

  (* The error here is calculated based on error rate given a key, not packet.
     And it is only an approximate estimate.
     collision_rate = 1 - (1 - 1/2^fp_len)^(#keys_per_slot - 1)
     error_rate = #slots * [ collision_rate * (#keys_per_slot - 1)
                           + (1 - collision_rate) * #keys_per_slot] / #keys
  *)
  let get_utility (w_pure_int : int) (time_hi : Z.t) (id : int) (syn : syninfo)
      (opt : opt_rec) (alloc : alloc_rec) (input_spec_map : input_map) : float =
    let du =
      if alloc.num_32b_fp = 0 then F.zero
      else
        let search_key = string_of_int id ^ "/dist_count" in
        let target_time, hkey_dist_count_tot_target =
          try StrMap.find input_spec_map search_key
          with Not_found ->
            raise
              (Error
                 (Printf.sprintf
                    "[InputSpec] The required input specification %s not \
                     providied"
                    search_key ) )
        in
        let hkey_dist_count_tot =
          F.mul
            (F.div hkey_dist_count_tot_target (Z.to_float target_time))
            (Z.to_float time_hi)
        in
        let num_slot = float_of_int (int_pow2 alloc.num_slot_log2) in
        let prob_base = Z.to_float (z_pow2 num_bit_prob) in
        let hkey_dist_count_list =
          slice_num prob_base alloc.r
          |> List.map (fun i -> hkey_dist_count_tot /. prob_base *. F.of_int i)
        in
        let for_each_row (hkey_dist_count : float) =
          let num_filled_slot =
            F.mul num_slot
              (F.sub 1. (F.pow (F.sub 1. (F.div 1. num_slot)) hkey_dist_count))
          in
          let num_keys_per_slot = F.div hkey_dist_count num_filled_slot in
          let num_32b_key = int_cdiv opt.key_length num_bit_timekey in
          let no_collision_rate =
            if alloc.num_32b_fp = num_32b_key then 1.
            else
              F.pow
                (F.sub 1.
                   (F.div 1.
                      (Z.to_float
                         (z_pow2 (num_bit_timekey * alloc.num_32b_fp)) ) ) )
                (F.sub num_keys_per_slot 1.)
          in
          F.mul num_filled_slot
            (F.add
               (F.mul no_collision_rate (F.sub num_keys_per_slot 1.))
               (F.mul (F.sub 1. no_collision_rate) num_keys_per_slot) )
        in
        F.div
          (List.fold_left
             (fun agg hkey_dist_count -> for_each_row hkey_dist_count +. agg)
             0. hkey_dist_count_list )
          hkey_dist_count_tot
    in
    du
  (* F.mul opt.qweight du *)

  let get_res_nodes_in_tup (stage_hash : int) (stage_action : int)
      (max_hash_per_table : int) (min_bit_per_hash : int) (num_bit_in_ts : int)
      (max_idx_per_phv : int) (num_unit : Z.t) (unit_len_log2 : int)
      (atomize : bool) (syn : syninfo) (opt : opt_rec) (alloc : alloc_rec) =
    let key_node =
      [ { typ=
            ( if atomize then
                Atom (if opt.num_dist_keys > 1 then true else false)
              else Table (if opt.num_dist_keys > 1 then true else false) )
        ; num_tbl= 1
        ; num_act=
            ( (if opt.num_dist_keys > 1 then opt.num_dist_keys else 1)
            + if syn.has_clear_branch then 1 else 0 )
        ; num_hash= 0
        ; num_reg= 0
        ; num_block= 0 } ]
    in
    let num_hash_per_index = int_cdiv alloc.num_slot_log2 min_bit_per_hash in
    let num_hash_per_prob = int_cdiv num_bit_prob min_bit_per_hash in
    if
      max_hash_per_table / num_hash_per_index = 0
      || max_hash_per_table / num_hash_per_prob = 0
    then
      raise
        (Error
           "[Alloc] Unsupported: it requires multiple tables to generate one \
            hash/clear index." ) ;
    let hash_nodes =
      if opt.num_dist_keys = 0 then []
      else
        let index_hash_node =
          { typ= Hash false
          ; num_tbl= 1
          ; num_act= 1
          ; num_hash= num_hash_per_index
          ; num_reg= 0
          ; num_block= 0 }
        in
        let prob_hash_node =
          { typ= Hash true
          ; num_tbl= 1
          ; num_act= 1
          ; num_hash= num_hash_per_prob
          ; num_reg= 0
          ; num_block= 0 }
        in
        [index_hash_node; prob_hash_node]
    in
    let clear_node =
      if alloc.w = 1 then []
      else if
        num_unit = Z.one
        && alloc.w land (alloc.w - 1) = 0
        && unit_len_log2 + int_log2up alloc.w <= num_bit_in_ts
      then []
      else
        [ { typ= Clear (true, true)
          ; num_tbl= 1
          ; num_act= 1 (* Hash unit seems not needed *)
          ; num_hash= 0
          ; num_reg= 1
          ; num_block= 1 } ]
    in
    let api_node =
      if alloc.w = 1 then []
      else
        [ { typ= (if atomize then Atom true else Table true)
          ; num_tbl= 1
          ; num_act= (if alloc.timestamp then 1 else alloc.w)
          ; num_hash= 0
          ; num_reg= 0
          ; num_block= 0 } ]
    in
    let reg_node =
      let num_act = opt.num_reg_progs + 1 in
      let num_reg = alloc.r * alloc.w in
      let timekey_nodes =
        if alloc.num_32b_fp = 0 then
          [ { typ= Reg true
            ; num_tbl= 1
            ; num_act= 1
            ; num_hash= num_hash_per_index
            ; num_reg
            ; num_block= alloc.block } ]
        else
          let rec gen_keys_nodes (num_fps : int) =
            if num_fps = 0 then []
            else
              let curr_num_fps = if num_fps = 1 then 1 else 2 in
              let remaining_num_fps = num_fps - curr_num_fps in
              list_repeat curr_num_fps
                { typ= Hash true
                ; num_tbl= 1
                ; num_act= 1
                ; num_hash= 2
                ; num_reg= 0
                ; num_block= 0 }
              @ [ { typ= Reg true
                  ; num_tbl= 1
                  ; num_act= 2
                  ; num_hash= num_hash_per_index
                  ; num_reg
                  ; num_block= alloc.block * curr_num_fps } ]
              @ gen_keys_nodes remaining_num_fps
          in
          [ { typ= Hash true
            ; num_tbl= 1
            ; num_act= 1
            ; num_hash= 2
            ; num_reg= 0
            ; num_block= 0 }
          ; { typ= Reg true
            ; num_tbl= 1
            ; num_act= 2
            ; num_hash= num_hash_per_index
            ; num_reg
            ; num_block= alloc.block * 2 } ]
          @ gen_keys_nodes (alloc.num_32b_fp - 1)
      in
      let value_nodes =
        [ { typ= Reg true
          ; num_tbl= 1
          ; num_act
          ; num_hash= num_hash_per_index
          ; num_reg
          ; num_block= alloc.block * opt.num_entries } ]
      in
      timekey_nodes @ value_nodes
    in
    let cap_node =
      match syn.api_set with
      | ASI ->
          []
      | _ ->
          let end_cap_node =
            [ { typ= (if atomize then Atom false else Table false)
              ; num_tbl= 1
              ; num_act= alloc.w * alloc.r
              ; num_hash= 0
              ; num_reg= 0
              ; num_block= 0 } ]
          in
          end_cap_node
    in
    (key_node, hash_nodes, clear_node, api_node, reg_node, cap_node)

  let get_res_nodes (stage_hash : int) (stage_action : int)
      (max_hash_per_table : int) (min_bit_per_hash : int) (num_bit_in_ts : int)
      (max_idx_per_phv : int) (num_unit : Z.t) (unit_len_log2 : int)
      (atomize : bool) (syn : syninfo) (opt : opt_rec) (alloc : alloc_rec) :
      res_node list =
    let key_node, hash_nodes, clear_node, api_node, reg_node, cap_node =
      get_res_nodes_in_tup stage_hash stage_action max_hash_per_table
        min_bit_per_hash num_bit_in_ts max_idx_per_phv num_unit unit_len_log2
        atomize syn opt alloc
    in
    key_node @ hash_nodes @ clear_node @ api_node @ reg_node @ cap_node

  let dsname = "Fold"

  let get_type_decl (p : string) (num_bit_per_slot : int) (syn : syninfo)
      (alloc : alloc_rec) : code_type =
    let keys_bit_length = numeric_raw_ty_size syn.keys_ty in
    CodeP4
      ( [ gen_p4decltypedef (p ^ "index_t") alloc.num_slot_log2
        ; gen_p4decltypedef (p ^ "value_t") num_bit_per_slot
        ; gen_p4decltypedef (p ^ "key_t") keys_bit_length
        ; gen_p4decltypedef (p ^ "prob_t") num_bit_prob ]
      , []
      , []
      , []
      , [] )

  let get_ds_metadata_decl (p : string) (opt : opt_rec) (alloc : alloc_rec) :
      code_type =
    let pair_32b_decl : P4.coq_Declaration =
      DeclStruct
        ( noinfo
        , to_p4str "bit32_pair_t"
        , [ P4Alias.MkDeclarationField
              (noinfo, TypBit (Bigint.of_int 32), to_p4str "lo")
          ; P4Alias.MkDeclarationField
              (noinfo, TypBit (Bigint.of_int 32), to_p4str "hi") ] )
    in
    let win_md_decl : P4.coq_Declaration =
      DeclStruct
        ( noinfo
        , to_p4str_p p "win_md_t"
        , [ P4Alias.MkDeclarationField
              (noinfo, TypTypeName (to_p4str "api_t"), to_p4str "api") ]
          @ map_for_range
              (fun i ->
                P4Alias.MkDeclarationField
                  ( noinfo
                  , TypTypeName (to_p4str_p p "value_t")
                  , to_p4str ("rw_" ^ string_of_int i) ) )
              1 alloc.r )
    in
    let shared_md_decl : P4.coq_Declaration =
      DeclStruct
        ( noinfo
        , to_p4str_p p "shared_md_t"
        , [ P4Alias.MkDeclarationField
              ( noinfo
              , TypTypeName (to_p4str_p p "index_t")
              , to_p4str "hash_index" )
          ; P4Alias.MkDeclarationField
              ( noinfo
              , TypTypeName (to_p4str_p p "value_t")
              , to_p4str "curr_time" )
          ; P4Alias.MkDeclarationField
              ( noinfo
              , TypTypeName
                  (to_p4str
                     ( if opt.num_entries = 1 then p ^ "value_t"
                       else "bit32_pair_t" ) )
              , to_p4str "value" )
          ; P4Alias.MkDeclarationField
              (noinfo, TypTypeName (to_p4str_p p "prob_t"), to_p4str "row_prob")
          ]
          @ map_for_range
              (fun i ->
                P4Alias.MkDeclarationField
                  ( noinfo
                  , TypTypeName (to_p4str_p p "value_t")
                  , to_p4str ("key_" ^ string_of_int i) ) )
              1 alloc.num_32b_fp )
    in
    let ds_md_decl : P4.coq_Declaration =
      DeclStruct
        ( noinfo
        , to_p4str_p p "ds_md_t"
        , ( if alloc.w = 1 then []
            else
              [ P4Alias.MkDeclarationField
                  ( noinfo
                  , TypTypeName (to_p4str "window_t")
                  , to_p4str "query_window" ) ] )
          @ [ P4Alias.MkDeclarationField
                ( noinfo
                , TypTypeName (to_p4str_p p "shared_md_t")
                , to_p4str "shared" ) ]
          @ map_for_range
              (fun i ->
                P4Alias.MkDeclarationField
                  ( noinfo
                  , TypTypeName (to_p4str_p p "win_md_t")
                  , to_p4str ("win_" ^ string_of_int i) ) )
              1 alloc.w )
    in
    CodeP4
      ([pair_32b_decl; win_md_decl; shared_md_decl; ds_md_decl], [], [], [], [])

  (* Same *)
  let get_metadata_fields (p : string) (alloc : alloc_rec) : code_type =
    let meta_fields =
      [ P4Alias.MkDeclarationField
          (noinfo, TypTypeName (to_p4str_p p "key_t"), to_p4str_p p "key")
      ; P4Alias.MkDeclarationField
          (noinfo, TypTypeName (to_p4str "api_t"), to_p4str_p p "api") ]
    in
    CodeP4 ([], meta_fields, [], [], [])

  let gen_p4dsmd (ss : string list) = gen_p4expname ("ds_md" :: ss)

  let gen_catdsmd (ss : string list) = gen_catname ("ds_md" :: ss)

  let gen_catexpdsmd (ss : string list) : Cat.exp =
    gen_catexpr (EVar (gen_catdsmd ss))

  let gen_vname_map (query_fun : query_fun) : string CidMap.t =
    let local_vars = get_read_var_from_query_fun false query_fun in
    let local_var_set = CidMap.create (List.length local_vars) in
    List.iter (fun var -> CidMap.replace local_var_set var ()) local_vars ;
    if CidMap.length local_var_set > 2 then
      raise (Error "[Bug] Fold can have at most two local variables.")
    else
      let vname_map = CidMap.create 2 in
      let p4_vnames = ["lo"; "hi"] in
      let _ =
        CidMap.fold
          (fun ident _ i ->
            CidMap.replace vname_map ident (List.nth p4_vnames i) ;
            i + 1 )
          local_var_set 0
      in
      vname_map

  let get_vname_decl (p : string) (opt : opt_rec) : code_type =
    CodeP4
      ( []
      , []
      , []
      , [ DeclVariable
            ( noinfo
            , TypTypeName
                (to_p4str
                   ( if opt.num_entries = 1 then p ^ "value_t"
                     else "bit32_pair_t" ) )
            , to_p4str "value"
            , None ) ]
      , [] )

  let get_key_decl (p : string) (vname_map : string CidMap.t) (syn : syninfo)
      (opt : opt_rec) : code_type =
    let fill_in_entry (keys_ids_list : (Cat.e list * int) list)
        ((pats, api, keys) : set_branch) : cat_entry =
      let matches = List.map (fun m -> MMatch m) pats in
      let action_name =
        match api with
        | AClear ->
            p ^ "act_set_noop_key"
        | _ -> (
          match get_from_fields keys keys_ids_list with
          | Some idx ->
              p ^ "act_set_key_" ^ string_of_int idx
          | None ->
              raise (Error "[Bug] Unexpected keys not found.") )
      in
      let api_vars =
        match api with
        | AInsert ->
            [gen_catexpname ["INSERT"]]
        | AQuery ->
            [gen_catexpname ["QUERY"]]
        | AInsQuery ->
            [gen_catexpname ["INSQUERY"]]
        | AClear ->
            []
      in
      MkCatEntry (matches, action_name, api_vars)
    in
    let create_key_action ((keys, idx) : Cat.e list * int) : cat_action =
      MkCatAction
        ( p ^ "act_set_key_" ^ string_of_int idx
        , [(Cat.ty (Cat.TInt (IConst num_bit_api_call)), "api")]
        , Cat.DSAssign (gen_catmeta [p ^ "api"], gen_catexpname ["api"])
          ::
          ( if opt.num_dist_keys > 1 then
              [Cat.DSAssign (gen_catmeta [p ^ "key"], snd (concat_keys keys))]
            else [] )
          @ CidMap.fold
              (fun ident p4_vname agg ->
                Cat.DSAssign
                  ( gen_catname
                      ( ["value"]
                      @ if opt.num_entries = 1 then [] else [p4_vname] )
                  , gen_catexpr
                      (EOp
                         ( Cast (IConst num_bit_per_slot)
                         , [gen_catexpr (EVar ident)] ) ) )
                :: agg )
              vname_map [] )
    in
    let keys_list =
      list_uniq (List.map (fun (_, _, keys) -> keys) syn.branches)
    in
    let ids = list_of_range 1 (List.length keys_list) in
    let keys_ids_list = List.combine keys_list ids in
    let key_actions = List.map create_key_action keys_ids_list in
    let noop_key_action =
      [ MkCatAction
          ( p ^ "act_set_noop_key"
          , []
          , [DSAssign (gen_catmeta [p ^ "api"], gen_catexpname ["NOOP"])] ) ]
    in
    let cactions =
      key_actions @ if syn.has_clear_branch then noop_key_action else []
    in
    let centries = List.map (fill_in_entry keys_ids_list) syn.branches in
    let ctable =
      MkCatTable
        ( p ^ "tbl_set_key"
        , syn.match_keys
        , list_repeat (List.length syn.match_keys) "ternary"
        , centries )
    in
    CodeTable (ctable, cactions)

  let get_ds_start (p : string) (dsname : string) (opt : opt_rec) : code_type =
    let cap_p =
      String.capitalize_ascii (String.sub p 0 (String.length p - 1))
    in
    let ds_name = cap_p ^ dsname in
    let args : param_tuple list =
      [ (In, TypTypeName (to_p4str_p p "key_t"), "ds_key")
      ; ( In
        , TypTypeName
            (to_p4str
               (if opt.num_entries = 1 then p ^ "value_t" else "bit32_pair_t") )
        , "ds_value" )
      ; (In, TypTypeName (to_p4str "api_t"), "api")
      ; (In, TypBit (Bigint.of_int 48), "ingress_mac_tstamp")
      ; (InOut, TypTypeName (to_p4str_p p "value_t"), "query_res") ]
    in
    CodeCtrlBegin (ds_name, args)

  let get_ds_md (p : string) : code_type =
    CodeP4
      ( []
      , []
      , []
      , [ DeclVariable
            ( noinfo
            , TypTypeName (to_p4str_p p "ds_md_t")
            , to_p4str "ds_md"
            , None ) ]
      , [] )

  let get_ds_end (p : string) (dsname : string) (var : Cid.t) (syn : syninfo)
      (opt : opt_rec) : code_type =
    let cap_p =
      String.capitalize_ascii (String.sub p 0 (String.length p - 1))
    in
    let instance_name = p ^ "ds" in
    let instance : P4.coq_Declaration =
      DeclInstantiation
        ( noinfo
        , TypSpecializedType (TypTypeName (to_p4str_p cap_p dsname), [])
        , []
        , to_p4str instance_name
        , [] )
    in
    let instance_call : P4.coq_StatementPreT =
      let str_to_exp = List.map (fun a -> Some (gen_p4expname a)) in
      let key =
        if opt.num_dist_keys = 0 then [Some (gen_p4expint 0 opt.key_length)]
        else if opt.num_dist_keys = 1 then (
          let keys_list =
            list_uniq (List.map (fun (_, _, keys) -> keys) syn.branches)
          in
          check_num_items keys_list 1
            "[DataStructShared] Expecting only one unique key sequence." ;
          let pkeys_p4 = concat_keys (List.hd keys_list) |> fst in
          [Some pkeys_p4] )
        else str_to_exp [["ig_md"; p ^ "key"]]
      in
      let in_args =
        str_to_exp
          [["value"]; ["ig_md"; p ^ "api"]; ["ig_intr_md"; "ingress_mac_tstamp"]]
      in
      StatMethodCall
        ( gen_p4expname [instance_name; "apply"]
        , []
        , key @ in_args @ [Some (trans_ident var)] )
    in
    CodeCtrlEnd ([], [], [], [instance], [instance_call])

  let get_clear_decl (abbr : int option) (unit_len_log2 : int) (num_unit : Z.t)
      (num_bit_in_ts : int) (alloc : alloc_rec) : code_type =
    match abbr with
    (* 1. w = 1; 2. w > 1 and x = 2^x *)
    | Some w_log_2 ->
        CodeP4 empty_prog_tuple
    | None ->
        let ig_decls : P4.coq_Declaration list =
          [ DeclInstantiation
              ( noinfo
              , TypSpecializedType
                  ( TypTypeName (to_p4str "Register")
                  , [ TypTypeName (to_p4str "window_pair_t")
                    ; TypBit (Bigint.of_int num_bit_clear_index) ] )
              , [ gen_p4expint 1 num_bit_reg_size_t
                ; gen_p4expr
                    (ExpList
                       [ gen_p4expint 0 num_bit_window_t
                       ; gen_p4expint 0 num_bit_window_t ] ) ]
              , to_p4str "reg_query_window"
              , [] )
          ; DeclInstantiation
              ( noinfo
              , TypSpecializedType
                  ( TypTypeName (to_p4str "RegisterAction")
                  , [ TypTypeName (to_p4str "window_pair_t")
                    ; TypBit (Bigint.of_int num_bit_clear_index)
                    ; TypTypeName (to_p4str "window_t") ] )
              , [str_to_expr "reg_query_window"]
              , to_p4str "regact_query_window_signal_0"
              , [ DeclFunction
                    ( noinfo
                    , TypVoid
                    , to_p4str "apply"
                    , []
                    , [ gen_p4param InOut
                          (TypTypeName (to_p4str "window_pair_t"))
                          "val"
                      ; gen_p4param Out (TypTypeName (to_p4str "window_t")) "rv"
                      ]
                    , prestmt_list_to_block
                        [ StatVariable
                            ( TypBool
                            , to_p4str "flip"
                            , Some
                                (gen_p4expr
                                   (ExpBinaryOp
                                      ( NotEq
                                      , gen_p4expname ["val"; "lo"]
                                      , gen_p4expint 0 num_bit_window_t ) ) )
                            , noloc )
                        ; StatVariable
                            ( TypBool
                            , to_p4str "wrap"
                            , Some
                                (gen_p4expr
                                   (ExpBinaryOp
                                      ( Eq
                                      , gen_p4expname ["val"; "hi"]
                                      , gen_p4expint
                                          ((Z.to_int num_unit * alloc.w) - 1)
                                          num_bit_window_t ) ) )
                            , noloc )
                        ; StatConditional
                            ( gen_p4expname ["flip"]
                            , gen_p4stmt
                                (StatBlock
                                   (prestmt_list_to_block
                                      [ StatConditional
                                          ( gen_p4expname ["wrap"]
                                          , gen_p4stmt
                                              (StatBlock
                                                 (prestmt_list_to_block
                                                    [ StatAssignment
                                                        ( gen_p4expname
                                                            ["val"; "lo"]
                                                        , gen_p4expint 0
                                                            num_bit_window_t )
                                                    ; StatAssignment
                                                        ( gen_p4expname
                                                            ["val"; "hi"]
                                                        , gen_p4expint 0
                                                            num_bit_window_t )
                                                    ] ) )
                                          , Some
                                              (gen_p4stmt
                                                 (StatBlock
                                                    (prestmt_list_to_block
                                                       [ StatAssignment
                                                           ( gen_p4expname
                                                               ["val"; "lo"]
                                                           , gen_p4expint 0
                                                               num_bit_window_t
                                                           )
                                                       ; StatAssignment
                                                           ( gen_p4expname
                                                               ["val"; "hi"]
                                                           , gen_p4expr
                                                               (ExpBinaryOp
                                                                  ( Plus
                                                                  , gen_p4expname
                                                                      [ "val"
                                                                      ; "hi" ]
                                                                  , gen_p4expint
                                                                      1
                                                                      num_bit_window_t
                                                                  ) ) ) ] ) ) )
                                          ) ] ) )
                            , Some
                                (gen_p4stmt
                                   (StatBlock
                                      (prestmt_list_to_block
                                         [ StatAssignment
                                             ( gen_p4expname ["val"; "lo"]
                                             , gen_p4expname ["val"; "lo"] )
                                         ; StatAssignment
                                             ( gen_p4expname ["val"; "hi"]
                                             , gen_p4expname ["val"; "hi"] ) ] )
                                   ) ) )
                        ; StatAssignment
                            (gen_p4expname ["rv"], gen_p4expname ["val"; "hi"])
                        ] ) ] )
          ; DeclInstantiation
              ( noinfo
              , TypSpecializedType
                  ( TypTypeName (to_p4str "RegisterAction")
                  , [ TypTypeName (to_p4str "window_pair_t")
                    ; TypBit (Bigint.of_int num_bit_clear_index)
                    ; TypTypeName (to_p4str "window_t") ] )
              , [str_to_expr "reg_query_window"]
              , to_p4str "regact_query_window_signal_1"
              , [ DeclFunction
                    ( noinfo
                    , TypVoid
                    , to_p4str "apply"
                    , []
                    , [ gen_p4param InOut
                          (TypTypeName (to_p4str "window_pair_t"))
                          "val"
                      ; gen_p4param Out (TypTypeName (to_p4str "window_t")) "rv"
                      ]
                    , prestmt_list_to_block
                        [ StatConditional
                            ( gen_p4expr
                                (ExpBinaryOp
                                   ( NotEq
                                   , gen_p4expname ["val"; "lo"]
                                   , gen_p4expint 1 num_bit_window_t ) )
                            , gen_p4stmt
                                (StatBlock
                                   (prestmt_list_to_block
                                      [ StatAssignment
                                          ( gen_p4expname ["val"; "lo"]
                                          , gen_p4expint 1 num_bit_window_t ) ] )
                                )
                            , None )
                        ; StatAssignment
                            (gen_p4expname ["rv"], gen_p4expname ["val"; "hi"])
                        ] ) ] )
          ; gen_p4act "act_query_window_signal_0"
              [ StatAssignment
                  ( gen_p4dsmd ["query_window"]
                  , gen_p4expr
                      (ExpFunctionCall
                         ( gen_p4expname
                             ["regact_query_window_signal_0"; "execute"]
                         , []
                         , [Some (gen_p4expint 0 num_bit_clear_index)] ) ) ) ]
          ; gen_p4act "act_query_window_signal_1"
              [ StatAssignment
                  ( gen_p4dsmd ["query_window"]
                  , gen_p4expr
                      (ExpFunctionCall
                         ( gen_p4expname
                             ["regact_query_window_signal_1"; "execute"]
                         , []
                         , [Some (gen_p4expint 0 num_bit_clear_index)] ) ) ) ]
          ; DeclTable
              ( noinfo
              , to_p4str "tbl_query_window"
              , [ MkTableKey
                    ( noinfo
                    , gen_p4expname ["ingress_mac_tstamp"]
                    , to_p4str "ternary" ) ]
              , [ gen_p4actref_na "act_query_window_signal_0"
                ; gen_p4actref_na "act_query_window_signal_1" ]
              , Some
                  [ gen_p4entry_na
                      [ MatchMask
                          ( gen_p4expint 0 num_bit_in_ts
                          , gen_p4expint
                              (int_pow2 (unit_len_log2 - 1))
                              num_bit_in_ts ) ]
                      "act_query_window_signal_0"
                  ; gen_p4entry_na [MatchDontCare] "act_query_window_signal_1"
                  ]
              , Some (gen_p4actref_na "act_query_window_signal_1")
              , Some (Bigint.of_int 2)
              , [] ) ]
        in
        let ig_ctrl = [gen_p4tbl_call "tbl_query_window"] in
        CodeP4 ([], [], [], ig_decls, ig_ctrl)

  let get_hash_decl (p : string) (abbr : int option)
      (index_poly_salt :
        (P4.coq_Declaration * (int * int) option * string) option )
      (prob_poly_salt :
        (P4.coq_Declaration * (int * int) option * string) option )
      (index_crc_bit : int) (prob_crc_bit : int) (unit_len_log2 : int)
      (num_unit : Z.t) (num_bit_in_ts : int) (opt : opt_rec) (alloc : alloc_rec)
      : code_type =
    let index_hash : P4.coq_Declaration list =
      (match index_poly_salt with None -> [] | Some (decl, _, _) -> [decl])
      @ [ DeclInstantiation
            ( noinfo
            , TypSpecializedType
                ( TypTypeName (to_p4str "Hash")
                , [TypBit (Bigint.of_int index_crc_bit)] )
            , ( if alloc.num_32b_fp = 0 then
                  [gen_p4expname ["HashAlgorithm_t"; "IDENTITY"]]
                else
                  [ gen_p4expname ["HashAlgorithm_t"; "CUSTOM"]
                  ; gen_p4expname ["poly_idx"] ] )
            , to_p4str "hash_idx"
            , [] )
        ; gen_p4act "act_hash_index"
            ( [ P4Alias.StatAssignment
                  ( gen_p4dsmd ["shared"; "hash_index"]
                  , gen_p4expr
                      (ExpBitStringAccess
                         ( gen_p4expr
                             (ExpFunctionCall
                                ( gen_p4expname ["hash_idx"; "get"]
                                , []
                                , [ Some
                                      ( match index_poly_salt with
                                      | Some (_, Some (v, w), _) ->
                                          gen_p4expr
                                            (ExpBinaryOp
                                               ( PlusPlus
                                               , gen_p4expname ["ds_key"]
                                               , gen_p4expint v w ) )
                                      | _ ->
                                          gen_p4expname ["ds_key"] ) ] ) )
                         , Bigint.zero
                         , Bigint.of_int (alloc.num_slot_log2 - 1) ) ) )
              ; StatAssignment
                  (gen_p4dsmd ["shared"; "value"], gen_p4expname ["ds_value"])
              ; StatAssignment
                  ( gen_p4dsmd ["shared"; "curr_time"]
                  , let bit_end =
                      match abbr with
                      | Some 0 ->
                          unit_len_log2
                      | _ ->
                          max (max_bit_reg_ts - 1)
                            (Z.log2
                               (Z.( - )
                                  (Z.( * )
                                     (Z.( * ) num_unit (z_pow2 unit_len_log2))
                                     (Z.of_int alloc.w) )
                                  Z.one ) )
                    in
                    let end_ts =
                      min (num_bit_in_ts - 1)
                        (bit_end + (num_bit_timekey - max_bit_reg_ts))
                    in
                    gen_p4expr
                      (ExpBitStringAccess
                         ( gen_p4expname ["ingress_mac_tstamp"]
                         , Bigint.of_int (end_ts - num_bit_timekey + 1)
                         , Bigint.of_int end_ts ) ) ) ]
            @
            match abbr with
            | None ->
                []
            | Some 0 ->
                [ P4Alias.StatAssignment
                    (gen_p4dsmd ["win_1"; "api"], gen_p4expname ["api"]) ]
            | Some w_log_2 ->
                [ P4Alias.StatAssignment
                    ( gen_p4dsmd ["query_window"]
                    , gen_p4expr
                        (ExpCast
                           ( TypTypeName (to_p4str "window_t")
                           , gen_p4expr
                               (ExpBitStringAccess
                                  ( gen_p4expname ["ingress_mac_tstamp"]
                                  , Bigint.of_int unit_len_log2
                                  , Bigint.of_int (unit_len_log2 + w_log_2 - 1)
                                  ) ) ) ) ) ] )
        ; gen_p4tbl "tbl_hash_index" "act_hash_index" ]
    in
    let prob_hash : P4.coq_Declaration list =
      (match prob_poly_salt with None -> [] | Some (decl, _, _) -> [decl])
      @ [ DeclInstantiation
            ( noinfo
            , TypSpecializedType
                ( TypTypeName (to_p4str "Hash")
                , [TypBit (Bigint.of_int prob_crc_bit)] )
            , ( if alloc.num_32b_fp = 0 then
                  [gen_p4expname ["HashAlgorithm_t"; "IDENTITY"]]
                else
                  [ gen_p4expname ["HashAlgorithm_t"; "CUSTOM"]
                  ; gen_p4expname ["poly_prob"] ] )
            , to_p4str "hash_prob"
            , [] )
        ; gen_p4act "act_row_prob"
            [ StatAssignment
                ( gen_p4dsmd ["shared"; "row_prob"]
                , gen_p4expr
                    (ExpFunctionCall
                       ( gen_p4expname ["hash_prob"; "get"]
                       , []
                       , if alloc.num_32b_fp = 0 then
                           [ Some
                               (gen_p4expr
                                  (ExpBinaryOp
                                     ( PlusPlus
                                     , gen_p4expint 0
                                         (prob_crc_bit - int_log2 alloc.r)
                                     , gen_p4expr
                                         (ExpBitStringAccess
                                            ( gen_p4expname ["ds_key"]
                                            , Bigint.of_int alloc.num_slot_log2
                                            , Bigint.of_int (opt.key_length - 1)
                                            ) ) ) ) ) ]
                         else
                           [ Some
                               ( match prob_poly_salt with
                               | Some (_, Some (v, w), _) ->
                                   gen_p4expr
                                     (ExpBinaryOp
                                        ( PlusPlus
                                        , gen_p4expname ["ds_key"]
                                        , gen_p4expint v w ) )
                               | _ ->
                                   gen_p4expname ["ds_key"] ) ] ) ) ) ]
        ; gen_p4tbl "tbl_row_prob" "act_row_prob" ]
    in
    let ig_ctrl =
      [gen_p4tbl_call "tbl_hash_index"; gen_p4tbl_call "tbl_row_prob"]
    in
    CodeP4 ([], [], [], index_hash @ prob_hash, ig_ctrl)

  let get_api_decl (p : string) (num_unit : Z.t) (syn : syninfo)
      (alloc : alloc_rec) : code_type =
    if alloc.w = 1 then CodeP4 empty_prog_tuple
    else
      let create_api_action (clear_win : int) : cat_action =
        let assign_win_api (curr_win : int) : Cat.dag_stmt =
          let curr_win = string_of_int curr_win in
          DSAssign
            ( gen_catdsmd ["win_" ^ curr_win; "api"]
            , gen_catexpname ["api_" ^ curr_win] )
        in
        let action_body = map_for_range assign_win_api 1 alloc.w in
        let params =
          map_for_range
            (fun i ->
              ( Cat.ty (Cat.TInt (IConst num_bit_api_call))
              , "api_" ^ string_of_int i ) )
            1 alloc.w
        in
        MkCatAction
          ("act_set_clear_win_" ^ string_of_int clear_win, params, action_body)
      in
      let cactions = map_for_range create_api_action 1 1 in
      let create_entries (key : string) (gen_act_args : int -> int -> Cat.exp) :
          cat_entry list =
        let create_entry (clear_win : int) =
          MkCatEntry
            ( [ MIdent (gen_catname [key])
              ; MMatch
                  (Cat.PRange
                     ( ( Z.( * ) (Z.of_int (clear_win - 1)) num_unit
                       , Some (IConst num_bit_window_t) )
                     , ( Z.( - ) (Z.( * ) (Z.of_int clear_win) num_unit) Z.one
                       , Some (IConst num_bit_window_t) ) ) ) ]
            , "act_set_clear_win_1"
            , map_for_range (gen_act_args (clear_win - 1)) 0 (alloc.w - 1) )
        in
        map_for_range create_entry 1 alloc.w
      in
      let centries_insert =
        let gen_act_args (clear_win : int) (i : int) =
          if i = (clear_win - 1 + alloc.w) mod alloc.w then
            gen_catexpname ["INSERT"]
          else gen_catexpname ["UPDATE"]
        in
        create_entries "INSERT" gen_act_args
      in
      let centries_query =
        let gen_act_args (clear_win : int) (i : int) =
          if i = clear_win then gen_catexpname ["QUERY"]
          else gen_catexpname ["NOOP"]
        in
        create_entries "QUERY" gen_act_args
      in
      let centries_insquery =
        let gen_act_args (clear_win : int) (i : int) =
          if i = clear_win then gen_catexpname ["UPDQUERY"]
          else if i = (clear_win - 1 + alloc.w) mod alloc.w then
            gen_catexpname ["INSERT"]
          else gen_catexpname ["UPDATE"]
        in
        create_entries "INSQUERY" gen_act_args
      in
      let centries_noop =
        let gen_act_args (clear_win : int) (i : int) =
          gen_catexpname ["NOOP"]
        in
        create_entries "NOOP" gen_act_args
      in
      let ks = [gen_catexpname ["api"]; gen_catexpdsmd ["query_window"]] in
      let mks = ["ternary"; "range"] in
      let centries =
        let win_entries =
          match syn.api_set with
          | ASQ ->
              centries_query
          | ASI ->
              centries_insert
          | ASInQ ->
              centries_insquery
          | ASIQ ->
              centries_insert @ centries_query
          | ASIInQ ->
              centries_insert @ centries_insquery
          | ASQInQ ->
              centries_query @ centries_insquery
          | ASIQInQ ->
              centries_insert @ centries_query @ centries_insquery
        in
        win_entries
        @ (if syn.has_clear_branch then centries_noop else [])
        @ [cat_act_dft (List.length ks)]
      in
      let ctable = MkCatTable ("tbl_set_win", ks, mks, centries) in
      CodeTable (ctable, cactions)

  let index_to_ident (field : int) (num_entries : int) =
    if field = 0 then
      gen_catname (if num_entries = 1 then ["val"] else ["val"; "lo"])
    else if field = 1 then gen_catname ["val"; "hi"]
    else raise (Error "[Bug] Unexpected state index in Fold.")

  (*
    Assumptions:
      1. The number of local vars <= 2; The number of state vars <= if init then 0 else number of entries
      2. 2 distinct conditions at most, translated into the standard form
      3. Every expression is allowed: 2 variables, Operation; each var only once
      4. pred and expression should type check
      5. ALU expressions not fully tested.
    *)
  let check_initupd (query_fun : query_fun) (vname_map : string CidMap.t) =
    match query_fun with
    | QFold (inits, upds, rv_idx) ->
        let num_entries = List.length inits in
        let is_state_var (cid : Cid.t) =
          match Cid.names cid with ["_s"; suffix] -> Some suffix | _ -> None
        in
        let check_atom_exp (exp : Cat.exp) =
          match exp.e with EInt _ | EVar _ -> true | _ -> false
        in
        let rec check_unary_logical (exp : Cat.exp) =
          match exp.e with
          | EOp (BitNot, [e1]) ->
              check_unary_logical e1
          | _ ->
              check_atom_exp exp
        in
        let check_binary_logical (exp : Cat.exp) =
          match exp.e with
          | EOp (BitAnd, [e1; e2])
          | EOp (BitXor, [e1; e2])
          | EOp (BitOr, [e1; e2]) ->
              check_unary_logical e1 && check_unary_logical e2
          | _ ->
              check_unary_logical exp
        in
        let rec check_logical_outer (exp : Cat.exp) =
          match exp.e with
          | EOp (BitNot, [e1]) ->
              check_logical_outer e1
          | _ ->
              check_binary_logical exp
        in
        let check_alu_exp (exp : Cat.exp) =
          match exp.e with
          | EOp (Plus, [e1; e2])
          | EOp (SatPlus, [e1; e2])
          | EOp (Sub, [e1; e2])
          | EOp (SatSub, [e1; e2]) ->
              check_atom_exp e1 && check_atom_exp e2
          | _ ->
              check_logical_outer exp
        in
        let check_upd_exp (e : Cat.exp) =
          let vars = get_read_var_from_expr e in
          let num_state_vars =
            List.length (List.filter_map is_state_var vars)
          in
          if num_state_vars > 1 then
            raise
              (Error
                 "[Bug] An expression in Fold can have at most one state \
                  variable." ) ;
          if List.length vars - num_state_vars > 1 then
            raise
              (Error
                 "[Bug] An expression in Fold can have at most one local \
                  variable." ) ;
          if check_alu_exp e then ()
          else raise (Error "[Bug] Expression too complex in Fold.")
        in
        let extract_atom_exp (ident_sign_map : bool CidMap.t) (exp : Cat.exp)
            (sign : bool) (tot : Z.t) =
          match exp.e with
          | EInt (value, _) ->
              if sign then Z.( + ) tot value else Z.( - ) tot value
          | EVar ident ->
              CidMap.add ident_sign_map ident sign ;
              tot
          | _ ->
              raise (Error "[Bug] Predicate too complex in Fold.")
        in
        let extract_unary_exp (ident_sign_map : bool CidMap.t) (exp : Cat.exp)
            (sign : bool) (tot : Z.t) =
          match exp.e with
          | EOp (Neg, [e1]) ->
              extract_atom_exp ident_sign_map e1 (not sign) tot
          | _ ->
              extract_atom_exp ident_sign_map exp sign tot
        in
        let rec extract_binary_exp (ident_sign_map : bool CidMap.t)
            (exp : Cat.exp) (sign : bool) (tot : Z.t) =
          match exp.e with
          | EOp (Plus, [e1; e2]) ->
              let tot = extract_unary_exp ident_sign_map e1 sign tot in
              extract_unary_exp ident_sign_map e2 sign tot
          | EOp (Sub, [e1; e2]) ->
              let tot = extract_unary_exp ident_sign_map e1 sign tot in
              extract_unary_exp ident_sign_map e2 (not sign) tot
          | _ ->
              extract_unary_exp ident_sign_map exp sign tot
        in
        let inequality_holds (op : compop) (tot : Z.t) =
          match op with
          | PLt ->
              tot < Z.zero
          | PGt ->
              tot > Z.zero
          | PLe ->
              tot <= Z.zero
          | PGe ->
              tot >= Z.zero
          | PEq ->
              tot = Z.zero
          | PNotEq ->
              tot <> Z.zero
        in
        let check_atom_pred (pred : predicate) =
          match pred with
          | PredComp (op, e1, e2) -> (
              let ident_sign_map = CidMap.create 3 in
              let tot = extract_binary_exp ident_sign_map e1 true Z.zero in
              let tot = extract_binary_exp ident_sign_map e2 false tot in
              let state_var_sign =
                CidMap.fold
                  (fun var sign agg ->
                    match (is_state_var var, agg) with
                    | None, _ ->
                        agg
                    | Some _, Some _ ->
                        raise
                          (Error
                             "[Bug] A predicate in Fold can have at most one \
                              state variable." )
                    | Some idx, None ->
                        Some (var, sign) )
                  ident_sign_map None
              in
              let local_var_sign =
                CidMap.fold
                  (fun var sign agg ->
                    match (is_state_var var, agg) with
                    | Some _, _ ->
                        agg
                    | None, Some _ ->
                        raise
                          (Error
                             "[Bug] A predicate in Fold can have at most one \
                              local variable." )
                    | None, None ->
                        Some (var, sign) )
                  ident_sign_map None
              in
              let tot = Z.( land ) (Z.( - ) (z_pow2 32) Z.one) tot in
              let neg_tot =
                Z.( land ) (Z.( - ) (z_pow2 32) Z.one) (Z.neg tot)
              in
              match (state_var_sign, local_var_sign) with
              | None, None ->
                  if inequality_holds op tot then PSeedTrue else PSeedFalse
              | Some (var, true), None | None, Some (var, true) ->
                  PSeedSimp
                    ( op
                    , gen_catexpr (EVar var)
                    , gen_catexpint_z neg_tot num_bit_per_slot )
              | Some (var, false), None | None, Some (var, false) ->
                  PSeedSimp
                    ( rev_inequality op
                    , gen_catexpr (EVar var)
                    , gen_catexpint_z tot num_bit_per_slot )
              | Some (state_var, false), Some (local_var, false) ->
                  PSeedSimp
                    ( rev_inequality op
                    , gen_catexpr
                        (EOp
                           ( Plus
                           , [ gen_catexpr (EVar state_var)
                             ; gen_catexpr (EVar local_var) ] ) )
                    , gen_catexpint_z tot num_bit_per_slot )
              | Some (state_var, true), Some (local_var, false) ->
                  PSeedSimp
                    ( op
                    , gen_catexpr
                        (EOp
                           ( Sub
                           , [ gen_catexpr (EVar state_var)
                             ; gen_catexpr (EVar local_var) ] ) )
                    , gen_catexpint_z neg_tot num_bit_per_slot )
              | Some (state_var, false), Some (local_var, true) ->
                  PSeedSimp
                    ( rev_inequality op
                    , gen_catexpr
                        (EOp
                           ( Sub
                           , [ gen_catexpr (EVar local_var)
                             ; gen_catexpr (EVar state_var) ] ) )
                    , gen_catexpint_z tot num_bit_per_slot )
              | Some (state_var, true), Some (local_var, true) ->
                  PSeedSimp
                    ( op
                    , gen_catexpr
                        (EOp
                           ( Plus
                           , [ gen_catexpr (EVar state_var)
                             ; gen_catexpr (EVar local_var) ] ) )
                    , gen_catexpint_z neg_tot num_bit_per_slot ) )
          | _ ->
              raise (Error "[Bug] Predicate too complex in Fold.")
        in
        let unify_ineq_op (cond_idx_map : int PSeedMap.t)
            (pseed_tup : pred_comp) (new_idx : int) (neg_cond : bool) =
          let cond_idx, new_idx' =
            match PSeedMap.find_opt cond_idx_map pseed_tup with
            | Some name_idx ->
                (name_idx, new_idx)
            | None ->
                PSeedMap.add cond_idx_map pseed_tup new_idx ;
                (new_idx, new_idx + 1)
          in
          ((if neg_cond then PNameNot cond_idx else PNameInt cond_idx), new_idx')
        in
        let check_unary_pred (cond_idx_map : int PSeedMap.t) (pred : predicate)
            (agg_idx : int) =
          match pred with
          | PredNot p1 -> (
              let pseed = check_atom_pred p1 in
              match pseed with
              | PSeedSimp (op, e1, e2) -> (
                match op with
                | PLt | PLe | PEq ->
                    unify_ineq_op cond_idx_map (op, e1, e2) agg_idx true
                | PGt | PGe | PNotEq ->
                    unify_ineq_op cond_idx_map
                      (inv_comp_op op, e1, e2)
                      agg_idx false )
              | PSeedFalse ->
                  (PNameTrue, agg_idx)
              | PSeedTrue ->
                  (PNameFalse, agg_idx) )
          | _ -> (
              let pseed = check_atom_pred pred in
              match pseed with
              | PSeedSimp (op, e1, e2) -> (
                match op with
                | PLt | PLe | PEq ->
                    unify_ineq_op cond_idx_map (op, e1, e2) agg_idx false
                | PGt | PGe | PNotEq ->
                    unify_ineq_op cond_idx_map
                      (inv_comp_op op, e1, e2)
                      agg_idx true )
              | PSeedTrue ->
                  (PNameTrue, agg_idx)
              | PSeedFalse ->
                  (PNameFalse, agg_idx) )
        in
        let order_pred_name (and_or : bool) (pred1 : pred_name)
            (pred2 : pred_name) =
          match (pred1, pred2) with
          | PNameInt idx1, PNameInt idx2
          | PNameInt idx1, PNameNot idx2
          | PNameNot idx1, PNameInt idx2
          | PNameNot idx1, PNameNot idx2 ->
              if idx1 < idx2 then
                if and_or then PNameAnd (pred1, pred2)
                else PNameOr (pred1, pred2)
              else if idx1 > idx2 then
                if and_or then PNameAnd (pred2, pred1)
                else PNameOr (pred2, pred1)
              else pred1
          | _, _ ->
              raise (Error "[Bug] Unexpected predicate names.")
        in
        let check_binary_pred (cond_idx_map : int PSeedMap.t) (pred : predicate)
            (agg_idx : int) =
          match pred with
          | PredAnd (p1, p2) -> (
              let condname1, agg_idx =
                check_unary_pred cond_idx_map p1 agg_idx
              in
              let condname2, agg_idx =
                check_unary_pred cond_idx_map p2 agg_idx
              in
              match (condname1, condname2) with
              | PNameTrue, PNameTrue ->
                  (PNameTrue, agg_idx)
              | PNameFalse, _ | _, PNameFalse ->
                  (PNameFalse, agg_idx)
              | PNameTrue, _ ->
                  (condname2, agg_idx)
              | _, PNameTrue ->
                  (condname1, agg_idx)
              | _, _ ->
                  (order_pred_name true condname1 condname2, agg_idx) )
          | PredOr (p1, p2) -> (
              let condname1, agg_idx =
                check_unary_pred cond_idx_map p1 agg_idx
              in
              let condname2, agg_idx =
                check_unary_pred cond_idx_map p2 agg_idx
              in
              match (condname1, condname2) with
              | PNameTrue, _ | _, PNameTrue ->
                  (PNameTrue, agg_idx)
              | PNameFalse, PNameFalse ->
                  (PNameFalse, agg_idx)
              | PNameFalse, _ ->
                  (condname2, agg_idx)
              | _, PNameFalse ->
                  (condname1, agg_idx)
              | _, _ ->
                  (order_pred_name false condname1 condname2, agg_idx) )
          | _ ->
              check_unary_pred cond_idx_map pred agg_idx
        in
        let rec double_not (pred : predicate) =
          match pred with PredNot (PredNot p1) -> double_not p1 | _ -> pred
        in
        let demorgan_law (pred : predicate) =
          match pred with
          | PredNot (PredAnd (p1, p2)) ->
              PredOr (double_not (PredNot p1), double_not (PredNot p2))
          | PredNot (PredOr (p1, p2)) ->
              PredAnd (double_not (PredNot p1), double_not (PredNot p2))
          | _ ->
              double_not pred
        in
        let check_update (cond_idx_map : int PSeedMap.t) (upd : update)
            (agg_idx : int) =
          match upd with
          | UpdExp e ->
              check_upd_exp e ;
              ((PNameTrue, UpdExp e), agg_idx)
          | UpdTernary (cond, e1, e2) -> (
              check_upd_exp e1 ;
              check_upd_exp e2 ;
              let cond' = demorgan_law cond in
              let condname, agg_idx =
                check_binary_pred cond_idx_map cond' agg_idx
              in
              match condname with
              | PNameTrue ->
                  ((PNameTrue, UpdExp e1), agg_idx)
              | PNameFalse ->
                  ((PNameFalse, UpdExp e2), agg_idx)
              | _ ->
                  ((condname, UpdTernary (cond, e1, e2)), agg_idx) )
        in
        let neg_predname (condname : pred_name) =
          match condname with
          | PNameInt idx ->
              PNameNot idx
          | PNameNot idx ->
              PNameInt idx
          | _ ->
              raise (Error "[Bug] Unexpected predicate names.")
        in
        let trans_predname (condname : pred_name) (num_cond : int) =
          match condname with
          | PNameTrue | PNameFalse ->
              raise (Error "[Bug] Unexpected predicate names.")
          | PNameInt idx | PNameNot idx ->
              if num_cond = 2 then
                match
                  (order_pred_name true condname (PNameInt (3 - idx)), idx)
                with
                | PNameAnd (pred1, pred2), 1 ->
                    ( [ PNameAnd (pred1, pred2)
                      ; PNameAnd (pred1, neg_predname pred2) ]
                    , [ PNameAnd (neg_predname pred1, pred2)
                      ; PNameAnd (neg_predname pred1, neg_predname pred2) ] )
                | PNameAnd (pred1, pred2), 2 ->
                    ( [ PNameAnd (pred1, pred2)
                      ; PNameAnd (neg_predname pred1, pred2) ]
                    , [ PNameAnd (pred1, neg_predname pred2)
                      ; PNameAnd (neg_predname pred1, neg_predname pred2) ] )
                | _ ->
                    raise (Error "[Bug] Unexpected predicate names.")
              else ([condname], [neg_predname condname])
          | PNameAnd (pred1, pred2) ->
              ( [condname]
              , [ PNameAnd (neg_predname pred1, pred2)
                ; PNameAnd (pred1, neg_predname pred2)
                ; PNameAnd (neg_predname pred1, neg_predname pred2) ] )
          | PNameOr (pred1, pred2) ->
              ( [ PNameAnd (pred1, pred2)
                ; PNameAnd (pred1, neg_predname pred2)
                ; PNameAnd (neg_predname pred1, pred2) ]
              , [PNameAnd (neg_predname pred1, neg_predname pred2)] )
        in
        let rec convert_ident (exp : Cat.exp) =
          let new_e : Cat.e =
            match exp.e with
            | EVar cid ->
                let new_id =
                  match Cid.names cid with
                  | ["_s"; field] ->
                      index_to_ident (int_of_string field) num_entries
                  | _ ->
                      gen_catname
                        ( ["shared_md"; "value"]
                        @
                        if num_entries = 1 then []
                        else [CidMap.find vname_map cid] )
                in
                EVar new_id
            | EOp (op, [e]) ->
                EOp (op, [convert_ident e])
            | EOp (op, [e1; e2]) ->
                EOp (op, [convert_ident e1; convert_ident e2])
            | EInt _ ->
                exp.e
            | _ ->
                raise (Error "[Bug] Unexpected expression.")
          in
          Cat.exp_sp new_e exp.espan
        in
        let collect_upds (cond_stmt_map : Cat.dag_stmt list PNameMap.t)
            ((condname, updexp) : pred_name * update) (index : int)
            (num_cond : int) =
          let tup_list =
            match updexp with
            | UpdExp e ->
                [ ( condname
                  , Cat.DSAssign
                      (index_to_ident index num_entries, convert_ident e) ) ]
            | UpdTernary (_, e1, e2) ->
                let tru_cond, fls_cond = trans_predname condname num_cond in
                List.map
                  (fun cn ->
                    ( cn
                    , Cat.DSAssign
                        (index_to_ident index num_entries, convert_ident e1) )
                    )
                  tru_cond
                @ List.map
                    (fun cn ->
                      ( cn
                      , Cat.DSAssign
                          (index_to_ident index num_entries, convert_ident e2)
                      ) )
                    fls_cond
          in
          let add_upd ((condname, stmt) : pred_name * Cat.dag_stmt) =
            match PNameMap.find_opt cond_stmt_map condname with
            | None ->
                PNameMap.add cond_stmt_map condname [stmt]
            | Some stmts ->
                PNameMap.replace cond_stmt_map condname (stmt :: stmts)
          in
          List.iter add_upd tup_list
        in
        let query_prestmt =
          [ P4Alias.StatAssignment
              ( gen_p4expname ["rv"]
              , trans_expr
                  (gen_catexpr (EVar (index_to_ident rv_idx num_entries))) ) ]
        in
        let check_updates (upds : update list) =
          let cond_idx_map = PSeedMap.create max_reg_entries in
          let agg_idx, updexps =
            fold_for_range
              (fun i (agg_idx, updexps) ->
                let updexp, agg_idx' =
                  check_update cond_idx_map (List.nth upds i) agg_idx
                in
                (agg_idx', updexp :: updexps) )
              0 (num_entries - 1) (1, [])
          in
          if agg_idx > 3 then
            raise (Error "[Bug] Fold can have at most two unique comparisons.")
          else
            let updexps = List.rev updexps in
            let num_cond = PSeedMap.length cond_idx_map in
            let cond_stmt_map = PNameMap.create 4 in
            iter_for_range
              (fun i ->
                collect_upds cond_stmt_map (List.nth updexps i) i num_cond )
              0 (num_entries - 1) ;
            PSeedMap.fold
              (fun (op, e1, e2) idx agg ->
                P4Alias.StatVariable
                  ( TypBool
                  , to_p4str ("condition_" ^ string_of_int idx)
                  , Some
                      (trans_pred
                         (PredComp (op, convert_ident e1, convert_ident e2)) )
                  , noloc )
                :: agg )
              cond_idx_map []
            @ ( match num_cond with
              | 0 ->
                  []
              | 1 -> (
                  let cond_1 = PNameMap.find_opt cond_stmt_map (PNameInt 1) in
                  let cond_2 = PNameMap.find_opt cond_stmt_map (PNameNot 1) in
                  match (cond_1, cond_2) with
                  | None, None ->
                      []
                  | Some stmts1, Some stmts2 ->
                      [ P4Alias.StatConditional
                          ( gen_p4expname ["condition_1"]
                          , gen_p4stmt
                              (StatBlock
                                 (prestmt_list_to_block
                                    (List.map trans_prestmt stmts1) ) )
                          , Some
                              (gen_p4stmt
                                 (StatBlock
                                    (prestmt_list_to_block
                                       (List.map trans_prestmt stmts2) ) ) ) )
                      ]
                  | _, _ ->
                      raise (Error "[Bug] Unexpected predicate names.") )
              | 2 -> (
                  let cond_1 =
                    PNameMap.find_opt cond_stmt_map
                      (PNameAnd (PNameInt 1, PNameInt 2))
                  in
                  let cond_2 =
                    PNameMap.find_opt cond_stmt_map
                      (PNameAnd (PNameInt 1, PNameNot 2))
                  in
                  let cond_3 =
                    PNameMap.find_opt cond_stmt_map
                      (PNameAnd (PNameNot 1, PNameInt 2))
                  in
                  let cond_4 =
                    PNameMap.find_opt cond_stmt_map
                      (PNameAnd (PNameNot 1, PNameNot 2))
                  in
                  match (cond_1, cond_2, cond_3, cond_4) with
                  | None, None, None, None ->
                      []
                  | Some stmts1, Some stmts2, Some stmts3, Some stmts4 ->
                      [ P4Alias.StatConditional
                          ( gen_p4expname ["condition_1"]
                          , gen_p4stmt
                              (StatConditional
                                 ( gen_p4expname ["condition_2"]
                                 , gen_p4stmt
                                     (StatBlock
                                        (prestmt_list_to_block
                                           (List.map trans_prestmt stmts1) ) )
                                 , Some
                                     (gen_p4stmt
                                        (StatBlock
                                           (prestmt_list_to_block
                                              (List.map trans_prestmt stmts2) )
                                        ) ) ) )
                          , Some
                              (gen_p4stmt
                                 (StatConditional
                                    ( gen_p4expname ["condition_2"]
                                    , gen_p4stmt
                                        (StatBlock
                                           (prestmt_list_to_block
                                              (List.map trans_prestmt stmts3) )
                                        )
                                    , Some
                                        (gen_p4stmt
                                           (StatBlock
                                              (prestmt_list_to_block
                                                 (List.map trans_prestmt stmts4) )
                                           ) ) ) ) ) ) ]
                  | _, _, _, _ ->
                      raise (Error "[Bug] Unexpected predicate names.") )
              | _ ->
                  raise
                    (Error "[Bug] Fold can have at most two unique comparisons.")
              )
            @ ( match PNameMap.find_opt cond_stmt_map PNameTrue with
              | Some stmts ->
                  List.map trans_prestmt stmts
              | None ->
                  [] )
            @ ( match PNameMap.find_opt cond_stmt_map PNameFalse with
              | Some stmts ->
                  List.map trans_prestmt stmts
              | None ->
                  [] )
            @ query_prestmt
        in
        let res_init = check_updates inits in
        let res_upd = check_updates upds in
        (res_init, res_upd, query_prestmt)
    | _ ->
        raise (Error "[Bug] Unexpected aggregation term; should be AggFold.")

  let get_row_decl (p : string)
      (key_poly_salt_list :
        (P4.coq_Declaration * (int * int) option * string) list )
      (num_bit_in_ts : int) (unit_len_log2 : int) (num_unit : Z.t)
      (vname_map : string CidMap.t) (syn : syninfo) (opt : opt_rec)
      (alloc : alloc_rec) : prog_tuple =
    let time_win =
      match alloc.w with
      | 1 ->
          num_unit
      | _ ->
          let win_len = Z.( * ) num_unit (z_pow2 unit_len_log2) in
          let num_bit_end =
            max max_bit_reg_ts
              (Z.log2 (Z.( - ) (Z.( * ) win_len (Z.of_int alloc.w)) Z.one) + 1)
          in
          let time_shift =
            min (num_bit_in_ts - num_bit_timekey) (num_bit_end - max_bit_reg_ts)
          in
          Z.shift_right win_len time_shift
    in
    let sub_api_decl : P4.coq_Declaration list =
      [ DeclVariable
          (noinfo, TypTypeName (to_p4str "pred_t"), to_p4str "sub_api", None) ]
    in
    let timekey_type =
      if alloc.num_32b_fp = 0 then p ^ "value_t" else "bit32_pair_t"
    in
    let time_val = if alloc.num_32b_fp = 0 then ["val"] else ["val"; "lo"] in
    let timekey_reg_decl : P4.coq_Declaration list =
      [ P4Alias.DeclInstantiation
          ( noinfo
          , TypSpecializedType
              ( TypTypeName (to_p4str "Register")
              , [ TypTypeName (to_p4str timekey_type)
                ; TypTypeName (to_p4str_p p "index_t") ] )
          , [ gen_p4expint (int_pow2 alloc.num_slot_log2) num_bit_reg_size_t
            ; (let well_expired =
                 gen_p4expint 0x7FFFFFFF num_bit_timekey
                 (* Cannot do it due to a HW bug (reported) *)
                 (* gen_p4expint
                    (Z.to_int (Z.( - ) (z_pow2 num_bit_timekey) time_win))
                    num_bit_timekey *)
               in
               if alloc.num_32b_fp = 0 then well_expired
               else
                 gen_p4expr (ExpList [well_expired; gen_p4expname ["DONTCARE"]])
              ) ]
          , to_p4str "reg_timekey"
          , [] ) ]
    in
    let num_32b_key = int_cdiv opt.key_length num_bit_timekey in
    let extra_bit_concat = (num_32b_key * num_bit_timekey) - opt.key_length in
    let key_crc_bit =
      if List.mem num_bit_timekey [8; 16; 32] then num_bit_timekey
      else
        raise
          (Error
             "[Bug] Number of bits in time and fingerprint must be 8, 16, or \
              32." )
    in
    let gen_key_hash
        (tup : (P4.coq_Declaration * (int * int) option * string) option)
        (key : int) =
      let key = string_of_int key in
      match tup with
      | None ->
          [ P4Alias.DeclInstantiation
              ( noinfo
              , TypSpecializedType
                  ( TypTypeName (to_p4str "Hash")
                  , [TypBit (Bigint.of_int key_crc_bit)] )
              , [gen_p4expname ["HashAlgorithm_t"; "IDENTITY"]]
              , to_p4str ("hash_key_" ^ key)
              , [] )
          ; gen_p4act ("act_key_" ^ key)
              [ StatAssignment
                  ( gen_p4dsmd ["shared"; "key_" ^ key]
                  , gen_p4expr
                      (ExpFunctionCall
                         ( gen_p4expname ["hash_key_" ^ key; "get"]
                         , []
                         , if num_32b_key = 1 && extra_bit_concat <> 0 then
                             [ Some
                                 (gen_p4expr
                                    (ExpBinaryOp
                                       ( PlusPlus
                                       , gen_p4expint 0 extra_bit_concat
                                       , gen_p4expname ["ds_key"] ) ) ) ]
                           else
                             [ Some
                                 (gen_p4expr
                                    (ExpBitStringAccess
                                       ( gen_p4expname ["ds_key"]
                                       , Bigint.zero
                                       , Bigint.of_int num_bit_timekey ) ) ) ]
                         ) ) ) ]
          ; gen_p4tbl ("tbl_key_" ^ key) ("act_key_" ^ key) ]
      | Some (poly_decl, salt, _) ->
          [ poly_decl
          ; DeclInstantiation
              ( noinfo
              , TypSpecializedType
                  ( TypTypeName (to_p4str "Hash")
                  , [TypBit (Bigint.of_int key_crc_bit)] )
              , [ gen_p4expname ["HashAlgorithm_t"; "CUSTOM"]
                ; gen_p4expname ["poly_key_" ^ key] ]
              , to_p4str ("hash_key_" ^ key)
              , [] )
          ; gen_p4act ("act_key_" ^ key)
              [ StatAssignment
                  ( gen_p4dsmd ["shared"; "key_" ^ key]
                  , gen_p4expr
                      (ExpFunctionCall
                         ( gen_p4expname ["hash_key_" ^ key; "get"]
                         , []
                         , [ Some
                               ( match salt with
                               | Some (v, w) ->
                                   gen_p4expr
                                     (ExpBinaryOp
                                        ( PlusPlus
                                        , gen_p4expname ["ds_key"]
                                        , gen_p4expint v w ) )
                               | None ->
                                   gen_p4expname ["ds_key"] ) ] ) ) ) ]
          ; gen_p4tbl ("tbl_key_" ^ key) ("act_key_" ^ key) ]
    in
    let key_hash_decls =
      map_for_range
        (fun i ->
          gen_key_hash
            ( if alloc.num_32b_fp = num_32b_key then None
              else Some (List.nth key_poly_salt_list (i - 1)) )
            i )
        1 alloc.num_32b_fp
      |> List.flatten
    in
    let key_hash_ctrl =
      map_for_range
        (fun key -> gen_p4tbl_call ("tbl_key_" ^ string_of_int key))
        1 alloc.num_32b_fp
    in
    let timekey_act_decl =
      [ P4Alias.DeclInstantiation
          ( noinfo
          , TypSpecializedType
              ( TypTypeName (to_p4str "RegisterAction")
              , [ TypTypeName (to_p4str timekey_type)
                ; TypTypeName (to_p4str_p p "index_t")
                ; TypTypeName (to_p4str "pred_t") ] )
          , [gen_p4expname ["reg_timekey"]]
          , to_p4str "regact_timekey_insert"
          , [ DeclFunction
                ( noinfo
                , TypVoid
                , to_p4str "apply"
                , []
                , [ gen_p4param InOut (TypTypeName (to_p4str timekey_type)) "val"
                  ; gen_p4param Out (TypTypeName (to_p4str "pred_t")) "rv" ]
                , prestmt_list_to_block
                    ( [ P4Alias.StatVariable
                          ( TypBool
                          , to_p4str "expire"
                          , Some
                              (gen_p4expr
                                 (ExpBinaryOp
                                    ( Ge
                                    , gen_p4expr
                                        (ExpBinaryOp
                                           ( Minus
                                           , gen_p4expname
                                               ["shared_md"; "curr_time"]
                                           , gen_p4expname time_val ) )
                                    , gen_p4expint (Z.to_int time_win)
                                        num_bit_timekey ) ) )
                          , noloc ) ]
                    @ ( if alloc.num_32b_fp = 0 then []
                        else
                          [ P4Alias.StatVariable
                              ( TypBool
                              , to_p4str "same_key"
                              , Some
                                  (gen_p4expr
                                     (ExpBinaryOp
                                        ( Eq
                                        , gen_p4expname ["shared_md"; "key_1"]
                                        , gen_p4expname ["val"; "hi"] ) ) )
                              , noloc ) ] )
                    @ [ StatAssignment
                          ( gen_p4expname ["rv"]
                          , gen_p4expr
                              (ExpFunctionCall
                                 ( gen_p4expname ["this"; "predicate"]
                                 , []
                                 , [Some (gen_p4expname ["expire"])]
                                   @
                                   if alloc.num_32b_fp = 0 then
                                     [Some (gen_p4expr (ExpBool true))]
                                   else [Some (gen_p4expname ["same_key"])] ) )
                          )
                      ; StatConditional
                          ( gen_p4expname ["expire"]
                          , gen_p4stmt
                              (StatBlock
                                 (prestmt_list_to_block
                                    ( [ P4Alias.StatAssignment
                                          ( gen_p4expname time_val
                                          , gen_p4expname
                                              ["shared_md"; "curr_time"] ) ]
                                    @
                                    if alloc.num_32b_fp = 0 then []
                                    else
                                      [ StatAssignment
                                          ( gen_p4expname ["val"; "hi"]
                                          , gen_p4expname ["shared_md"; "key_1"]
                                          ) ] ) ) )
                          , None ) ] ) ) ] )
      ; gen_p4act "act_timekey_insert"
          [ StatAssignment
              ( gen_p4expname ["sub_api"]
              , gen_p4expr
                  (ExpFunctionCall
                     ( gen_p4expname ["regact_timekey_insert"; "execute"]
                     , []
                     , [Some (gen_p4expname ["shared_md"; "hash_index"])] ) ) )
          ] ]
      @
      if alloc.num_32b_fp = 0 then []
      else
        [ DeclInstantiation
            ( noinfo
            , TypSpecializedType
                ( TypTypeName (to_p4str "RegisterAction")
                , [ TypTypeName (to_p4str "bit32_pair_t")
                  ; TypTypeName (to_p4str_p p "index_t")
                  ; TypTypeName (to_p4str "pred_t") ] )
            , [gen_p4expname ["reg_timekey"]]
            , to_p4str "regact_timekey_query"
            , [ DeclFunction
                  ( noinfo
                  , TypVoid
                  , to_p4str "apply"
                  , []
                  , [ gen_p4param InOut
                        (TypTypeName (to_p4str "bit32_pair_t"))
                        "val"
                    ; gen_p4param Out (TypTypeName (to_p4str "pred_t")) "rv" ]
                  , prestmt_list_to_block
                      [ StatVariable
                          ( TypBool
                          , to_p4str "expire"
                          , Some
                              (gen_p4expr
                                 (ExpBinaryOp
                                    ( Ge
                                    , gen_p4expr
                                        (ExpBinaryOp
                                           ( Minus
                                           , gen_p4expname
                                               ["shared_md"; "curr_time"]
                                           , gen_p4expname ["val"; "lo"] ) )
                                    , gen_p4expint (Z.to_int time_win)
                                        num_bit_timekey ) ) )
                          , noloc )
                      ; StatVariable
                          ( TypBool
                          , to_p4str "same_key"
                          , Some
                              (gen_p4expr
                                 (ExpBinaryOp
                                    ( Eq
                                    , gen_p4expname ["shared_md"; "key_1"]
                                    , gen_p4expname ["val"; "hi"] ) ) )
                          , noloc )
                      ; StatAssignment
                          ( gen_p4expname ["rv"]
                          , gen_p4expr
                              (ExpFunctionCall
                                 ( gen_p4expname ["this"; "predicate"]
                                 , []
                                 , [ Some (gen_p4expname ["expire"])
                                   ; Some (gen_p4expname ["same_key"]) ] ) ) )
                      ] ) ] )
        ; gen_p4act "act_timekey_query"
            [ StatAssignment
                ( gen_p4expname ["sub_api"]
                , gen_p4expr
                    (ExpFunctionCall
                       ( gen_p4expname ["regact_timekey_query"; "execute"]
                       , []
                       , [Some (gen_p4expname ["shared_md"; "hash_index"])] ) )
                ) ] ]
    in
    let name = "tbl_timekey" in
    let ks =
      [gen_catexpname ["api"]; gen_catexpname ["shared_md"; "row_prob"]]
    in
    let mks = ["ternary"; "range"] in
    let centry_insert =
      MkCatEntry
        ( [ MIdent (gen_catname ["INSERT"])
          ; MRange (gen_catname ["prob_start"], gen_catname ["prob_end"]) ]
        , "act_timekey_insert"
        , [] )
    in
    let centry_insquery =
      MkCatEntry
        ( [ MIdent (gen_catname ["INSQUERY"])
          ; MRange (gen_catname ["prob_start"], gen_catname ["prob_end"]) ]
        , "act_timekey_insert"
        , [] )
    in
    let centry_update =
      MkCatEntry
        ( [ MIdent (gen_catname ["UPDATE"])
          ; MRange (gen_catname ["prob_start"], gen_catname ["prob_end"]) ]
        , ( if alloc.num_32b_fp = 0 then "act_timekey_insert"
            else "act_timekey_query" )
        , [] )
    in
    let centry_query =
      MkCatEntry
        ( [ MIdent (gen_catname ["QUERY"])
          ; MRange (gen_catname ["prob_start"], gen_catname ["prob_end"]) ]
        , ( if alloc.num_32b_fp = 0 then "act_timekey_insert"
            else "act_timekey_query" )
        , [] )
    in
    let centry_updquery =
      MkCatEntry
        ( [ MIdent (gen_catname ["UPDQUERY"])
          ; MRange (gen_catname ["prob_start"], gen_catname ["prob_end"]) ]
        , ( if alloc.num_32b_fp = 0 then "act_timekey_insert"
            else "act_timekey_query" )
        , [] )
    in
    let centries =
      let win_entries =
        match syn.api_set with
        | ASQ ->
            [centry_query]
        | ASI ->
            [centry_insert]
        | ASInQ ->
            if alloc.w = 1 then [centry_insquery]
            else [centry_insert; centry_update; centry_updquery]
        | ASIQ ->
            if alloc.w = 1 then [centry_insert; centry_query]
            else [centry_insert; centry_update; centry_query]
        | ASIInQ ->
            if alloc.w = 1 then [centry_insert; centry_insquery]
            else [centry_insert; centry_update; centry_updquery]
        | ASQInQ ->
            if alloc.w = 1 then [centry_query; centry_insquery]
            else [centry_insert; centry_update; centry_query; centry_updquery]
        | ASIQInQ ->
            if alloc.w = 1 then [centry_insert; centry_query; centry_insquery]
            else [centry_insert; centry_update; centry_query; centry_updquery]
      in
      win_entries @ [cat_act_dft (List.length ks)]
    in
    let ctable = MkCatTable (name, ks, mks, centries) in
    let timekey_table = trans_table ctable in
    let gen_key_decls (key : int) : P4.coq_Declaration list =
      let single = (2 * key) + 1 > alloc.num_32b_fp in
      let key_lo = ["shared_md"; "key_" ^ string_of_int (2 * key)] in
      let key_hi = ["shared_md"; "key_" ^ string_of_int ((2 * key) + 1)] in
      let val_lo = if single then ["val"] else ["val"; "lo"] in
      let key_type = if single then p ^ "value_t" else "bit32_pair_t" in
      let key = string_of_int key in
      let key_reg =
        [ P4Alias.DeclInstantiation
            ( noinfo
            , TypSpecializedType
                ( TypTypeName (to_p4str "Register")
                , [ TypTypeName (to_p4str key_type)
                  ; TypTypeName (to_p4str_p p "index_t") ] )
            , [gen_p4expint (int_pow2 alloc.num_slot_log2) num_bit_reg_size_t]
            , to_p4str ("reg_key_" ^ key)
            , [] ) ]
      in
      let action_insert =
        [ P4Alias.DeclInstantiation
            ( noinfo
            , TypSpecializedType
                ( TypTypeName (to_p4str "RegisterAction")
                , [ TypTypeName (to_p4str key_type)
                  ; TypTypeName (to_p4str_p p "index_t")
                  ; TypTypeName (to_p4str "pred_t") ] )
            , [gen_p4expname ["reg_key_" ^ key]]
            , to_p4str ("regact_key_insert_" ^ key)
            , [ DeclFunction
                  ( noinfo
                  , TypVoid
                  , to_p4str "apply"
                  , []
                  , [ gen_p4param InOut (TypTypeName (to_p4str key_type)) "val"
                    ; gen_p4param Out (TypTypeName (to_p4str "pred_t")) "rv" ]
                  , prestmt_list_to_block
                      ( [ P4Alias.StatAssignment
                            (gen_p4expname val_lo, gen_p4expname key_lo) ]
                      @
                      if single then []
                      else
                        [ StatAssignment
                            (gen_p4expname ["val"; "hi"], gen_p4expname key_hi)
                        ] ) ) ] )
        ; gen_p4act ("act_key_insert_" ^ key)
            [ StatMethodCall
                ( gen_p4expname ["regact_key_insert_" ^ key; "execute"]
                , []
                , [Some (gen_p4expname ["shared_md"; "hash_index"])] ) ] ]
      in
      let action_query =
        [ P4Alias.DeclInstantiation
            ( noinfo
            , TypSpecializedType
                ( TypTypeName (to_p4str "RegisterAction")
                , [ TypTypeName (to_p4str key_type)
                  ; TypTypeName (to_p4str_p p "index_t")
                  ; TypTypeName (to_p4str "pred_t") ] )
            , [gen_p4expname ["reg_key_" ^ key]]
            , to_p4str ("regact_key_query_" ^ key)
            , [ DeclFunction
                  ( noinfo
                  , TypVoid
                  , to_p4str "apply"
                  , []
                  , [ gen_p4param InOut (TypTypeName (to_p4str key_type)) "val"
                    ; gen_p4param Out (TypTypeName (to_p4str "pred_t")) "rv" ]
                  , prestmt_list_to_block
                      ( [ P4Alias.StatVariable
                            ( TypBool
                            , to_p4str "same_key_lo"
                            , Some
                                (gen_p4expr
                                   (ExpBinaryOp
                                      ( Eq
                                      , gen_p4expname val_lo
                                      , gen_p4expname key_lo ) ) )
                            , noloc ) ]
                      @ ( if single then []
                          else
                            [ P4Alias.StatVariable
                                ( TypBool
                                , to_p4str "same_key_hi"
                                , Some
                                    (gen_p4expr
                                       (ExpBinaryOp
                                          ( Eq
                                          , gen_p4expname ["val"; "hi"]
                                          , gen_p4expname key_hi ) ) )
                                , noloc ) ] )
                      @ [ P4Alias.StatConditional
                            ( ( if single then gen_p4expname ["same_key_lo"]
                                else
                                  gen_p4expr
                                    (ExpBinaryOp
                                       ( And
                                       , gen_p4expname ["same_key_lo"]
                                       , gen_p4expname ["same_key_hi"] ) ) )
                            , gen_p4stmt
                                (StatBlock
                                   (prestmt_list_to_block
                                      [ StatAssignment
                                          ( gen_p4expname ["rv"]
                                          , gen_p4expname ["sub_api"] ) ] ) )
                            , Some
                                (gen_p4stmt
                                   (StatBlock
                                      (prestmt_list_to_block
                                         [ StatAssignment
                                             ( gen_p4expname ["rv"]
                                             , gen_p4expname ["NOOP"] ) ] ) ) )
                            ) ] ) ) ] )
        ; gen_p4act ("act_key_query_" ^ key)
            [ StatAssignment
                ( gen_p4expname ["sub_api"]
                , gen_p4expr
                    (ExpFunctionCall
                       ( gen_p4expname ["regact_key_query_" ^ key; "execute"]
                       , []
                       , [Some (gen_p4expname ["shared_md"; "hash_index"])] ) )
                ) ] ]
      in
      let key_actions =
        match syn.api_set with
        | ASQ ->
            action_insert
        | ASI ->
            action_query
        | ASInQ | ASIQ | ASIInQ | ASQInQ | ASIQInQ ->
            action_insert @ action_query
      in
      let name = "tbl_key_" ^ key in
      let ks = [gen_catexpname ["api"]; gen_catexpname ["sub_api"]] in
      let mks = ["ternary"; "ternary"] in
      let centries_insert =
        [ MkCatEntry
            ( [ MIdent (gen_catname ["INSERT"])
              ; MMatch (PNum (Z.of_int 2, Some (IConst num_bit_pred))) ]
            , "act_key_insert_" ^ key
            , [] )
        ; MkCatEntry
            ( [ MIdent (gen_catname ["INSERT"])
              ; MMatch (PNum (Z.of_int 8, Some (IConst num_bit_pred))) ]
            , "act_key_insert_" ^ key
            , [] )
        ; MkCatEntry
            ( [ MIdent (gen_catname ["INSERT"])
              ; MMatch (PNum (Z.of_int 4, Some (IConst num_bit_pred))) ]
            , "act_key_query_" ^ key
            , [] ) ]
      in
      let centries_insquery =
        [ MkCatEntry
            ( [ MIdent (gen_catname ["INSQUERY"])
              ; MMatch (PNum (Z.of_int 2, Some (IConst num_bit_pred))) ]
            , "act_key_insert_" ^ key
            , [] )
        ; MkCatEntry
            ( [ MIdent (gen_catname ["INSQUERY"])
              ; MMatch (PNum (Z.of_int 8, Some (IConst num_bit_pred))) ]
            , "act_key_insert_" ^ key
            , [] )
        ; MkCatEntry
            ( [ MIdent (gen_catname ["INSQUERY"])
              ; MMatch (PNum (Z.of_int 4, Some (IConst num_bit_pred))) ]
            , "act_key_query_" ^ key
            , [] ) ]
      in
      let centries_update =
        [ MkCatEntry
            ( [ MIdent (gen_catname ["UPDATE"])
              ; MMatch (PNum (Z.of_int 8, Some (IConst num_bit_pred))) ]
            , "act_key_query_" ^ key
            , [] ) ]
      in
      let centries_query =
        [ MkCatEntry
            ( [ MIdent (gen_catname ["QUERY"])
              ; MMatch (PNum (Z.of_int 8, Some (IConst num_bit_pred))) ]
            , "act_key_query_" ^ key
            , [] ) ]
      in
      let centries_updquery =
        [ MkCatEntry
            ( [ MIdent (gen_catname ["UPDQUERY"])
              ; MMatch (PNum (Z.of_int 8, Some (IConst num_bit_pred))) ]
            , "act_key_query_" ^ key
            , [] ) ]
      in
      let centries =
        let win_entries =
          match syn.api_set with
          | ASQ ->
              centries_query
          | ASI ->
              centries_insert
          | ASInQ ->
              if alloc.w = 1 then centries_insquery
              else centries_insert @ centries_update @ centries_updquery
          | ASIQ ->
              if alloc.w = 1 then centries_insert @ centries_query
              else centries_insert @ centries_update @ centries_query
          | ASIInQ ->
              if alloc.w = 1 then centries_insert @ centries_insquery
              else centries_insert @ centries_update @ centries_updquery
          | ASQInQ ->
              if alloc.w = 1 then centries_query @ centries_insquery
              else
                centries_insert @ centries_update @ centries_query
                @ centries_updquery
          | ASIQInQ ->
              if alloc.w = 1 then
                centries_insert @ centries_query @ centries_insquery
              else
                centries_insert @ centries_update @ centries_query
                @ centries_updquery
        in
        win_entries @ [cat_act_dft (List.length ks)]
      in
      let ctable = MkCatTable (name, ks, mks, centries) in
      let value_table = trans_table ctable in
      key_reg @ key_actions @ [value_table]
    in
    let key_decls =
      map_for_range gen_key_decls 1 (int_cdiv (alloc.num_32b_fp - 1) 2)
      |> List.flatten
    in
    let key_ctrl =
      map_for_range
        (fun key -> gen_p4tbl_call ("tbl_key_" ^ string_of_int key))
        1
        (int_cdiv (alloc.num_32b_fp - 1) 2)
    in
    let init_prestmt, upd_prestmt, query_prestmt =
      check_initupd syn.query_fun vname_map
    in
    let value_type =
      if opt.num_entries = 1 then p ^ "value_t" else "bit32_pair_t"
    in
    let value_reg_decl =
      [ P4Alias.DeclInstantiation
          ( noinfo
          , TypSpecializedType
              ( TypTypeName (to_p4str "Register")
              , [ TypTypeName (to_p4str value_type)
                ; TypTypeName (to_p4str_p p "index_t") ] )
          , [gen_p4expint (int_pow2 alloc.num_slot_log2) num_bit_reg_size_t]
          , to_p4str "reg_value"
          , [] ) ]
    in
    let value_init_action =
      [ P4Alias.DeclInstantiation
          ( noinfo
          , TypSpecializedType
              ( TypTypeName (to_p4str "RegisterAction")
              , [ TypTypeName (to_p4str value_type)
                ; TypTypeName (to_p4str_p p "index_t")
                ; TypTypeName (to_p4str_p p "value_t") ] )
          , [gen_p4expname ["reg_value"]]
          , to_p4str "regact_value_init"
          , [ DeclFunction
                ( noinfo
                , TypVoid
                , to_p4str "apply"
                , []
                , [ gen_p4param InOut (TypTypeName (to_p4str value_type)) "val"
                  ; gen_p4param Out (TypTypeName (to_p4str_p p "value_t")) "rv"
                  ]
                , prestmt_list_to_block init_prestmt ) ] )
      ; gen_p4act "act_value_init"
          [ StatAssignment
              ( gen_p4expname ["rw"]
              , gen_p4expr
                  (ExpFunctionCall
                     ( gen_p4expname ["regact_value_init"; "execute"]
                     , []
                     , [Some (gen_p4expname ["shared_md"; "hash_index"])] ) ) )
          ] ]
    in
    let value_upd_action =
      [ P4Alias.DeclInstantiation
          ( noinfo
          , TypSpecializedType
              ( TypTypeName (to_p4str "RegisterAction")
              , [ TypTypeName (to_p4str value_type)
                ; TypTypeName (to_p4str_p p "index_t")
                ; TypTypeName (to_p4str_p p "value_t") ] )
          , [gen_p4expname ["reg_value"]]
          , to_p4str "regact_value_upd"
          , [ DeclFunction
                ( noinfo
                , TypVoid
                , to_p4str "apply"
                , []
                , [ gen_p4param InOut (TypTypeName (to_p4str value_type)) "val"
                  ; gen_p4param Out (TypTypeName (to_p4str_p p "value_t")) "rv"
                  ]
                , prestmt_list_to_block upd_prestmt ) ] )
      ; gen_p4act "act_value_upd"
          [ StatAssignment
              ( gen_p4expname ["rw"]
              , gen_p4expr
                  (ExpFunctionCall
                     ( gen_p4expname ["regact_value_upd"; "execute"]
                     , []
                     , [Some (gen_p4expname ["shared_md"; "hash_index"])] ) ) )
          ] ]
    in
    let value_query_action =
      [ P4Alias.DeclInstantiation
          ( noinfo
          , TypSpecializedType
              ( TypTypeName (to_p4str "RegisterAction")
              , [ TypTypeName (to_p4str value_type)
                ; TypTypeName (to_p4str_p p "index_t")
                ; TypTypeName (to_p4str_p p "value_t") ] )
          , [gen_p4expname ["reg_value"]]
          , to_p4str "regact_value_query"
          , [ DeclFunction
                ( noinfo
                , TypVoid
                , to_p4str "apply"
                , []
                , [ gen_p4param InOut (TypTypeName (to_p4str value_type)) "val"
                  ; gen_p4param Out (TypTypeName (to_p4str_p p "value_t")) "rv"
                  ]
                , prestmt_list_to_block query_prestmt ) ] )
      ; gen_p4act "act_value_query"
          [ StatAssignment
              ( gen_p4expname ["rw"]
              , gen_p4expr
                  (ExpFunctionCall
                     ( gen_p4expname ["regact_value_query"; "execute"]
                     , []
                     , [Some (gen_p4expname ["shared_md"; "hash_index"])] ) ) )
          ] ]
    in
    let value_act_decl =
      match syn.api_set with
      | ASQ ->
          value_query_action
      | ASI ->
          value_init_action @ value_upd_action
      | ASInQ | ASIInQ ->
          if alloc.w = 1 then value_init_action @ value_upd_action
          else value_init_action @ value_upd_action @ value_query_action
      | ASIQ | ASQInQ | ASIQInQ ->
          value_init_action @ value_upd_action @ value_query_action
    in
    let name = "tbl_value" in
    let ks = [gen_catexpname ["api"]; gen_catexpname ["sub_api"]] in
    let mks = ["ternary"; "ternary"] in
    let centries_insert =
      [ MkCatEntry
          ( [ MIdent (gen_catname ["INSERT"])
            ; MMatch (PNum (Z.of_int 2, Some (IConst num_bit_pred))) ]
          , "act_value_init"
          , [] )
      ; MkCatEntry
          ( [ MIdent (gen_catname ["INSERT"])
            ; MMatch (PNum (Z.of_int 8, Some (IConst num_bit_pred))) ]
          , "act_value_init"
          , [] )
      ; MkCatEntry
          ( [ MIdent (gen_catname ["INSERT"])
            ; MMatch (PNum (Z.of_int 4, Some (IConst num_bit_pred))) ]
          , "act_value_upd"
          , [] ) ]
    in
    let centries_insquery =
      [ MkCatEntry
          ( [ MIdent (gen_catname ["INSQUERY"])
            ; MMatch (PNum (Z.of_int 2, Some (IConst num_bit_pred))) ]
          , "act_value_init"
          , [] )
      ; MkCatEntry
          ( [ MIdent (gen_catname ["INSQUERY"])
            ; MMatch (PNum (Z.of_int 8, Some (IConst num_bit_pred))) ]
          , "act_value_init"
          , [] )
      ; MkCatEntry
          ( [ MIdent (gen_catname ["INSQUERY"])
            ; MMatch (PNum (Z.of_int 4, Some (IConst num_bit_pred))) ]
          , "act_value_upd"
          , [] ) ]
    in
    let centries_update =
      [ MkCatEntry
          ( [ MIdent (gen_catname ["UPDATE"])
            ; MMatch (PNum (Z.of_int 8, Some (IConst num_bit_pred))) ]
          , "act_value_upd"
          , [] ) ]
    in
    let centries_query =
      [ MkCatEntry
          ( [ MIdent (gen_catname ["QUERY"])
            ; MMatch (PNum (Z.of_int 8, Some (IConst num_bit_pred))) ]
          , "act_value_query"
          , [] ) ]
    in
    let centries_updquery =
      [ MkCatEntry
          ( [ MIdent (gen_catname ["UPDQUERY"])
            ; MMatch (PNum (Z.of_int 8, Some (IConst num_bit_pred))) ]
          , "act_value_upd"
          , [] ) ]
    in
    let centries =
      let win_entries =
        match syn.api_set with
        | ASQ ->
            centries_query
        | ASI ->
            centries_insert
        | ASInQ ->
            if alloc.w = 1 then centries_insquery
            else centries_insert @ centries_update @ centries_updquery
        | ASIQ ->
            if alloc.w = 1 then centries_insert @ centries_query
            else centries_insert @ centries_update @ centries_query
        | ASIInQ ->
            if alloc.w = 1 then centries_insert @ centries_insquery
            else centries_insert @ centries_update @ centries_updquery
        | ASQInQ ->
            if alloc.w = 1 then centries_query @ centries_insquery
            else
              centries_insert @ centries_update @ centries_query
              @ centries_updquery
        | ASIQInQ ->
            if alloc.w = 1 then
              centries_insert @ centries_query @ centries_insquery
            else
              centries_insert @ centries_update @ centries_query
              @ centries_updquery
      in
      win_entries @ [cat_act_dft (List.length ks)]
    in
    let ctable = MkCatTable (name, ks, mks, centries) in
    let value_table = trans_table ctable in
    let cap_p =
      String.capitalize_ascii (String.sub p 0 (String.length p - 1))
    in
    let ctrl =
      gen_p4ctrl
        ~cps:
          [ (Directionless, TypTypeName (to_p4str_p p "prob_t"), "prob_start")
          ; (Directionless, TypTypeName (to_p4str_p p "prob_t"), "prob_end") ]
        (cap_p ^ dsname ^ "Row")
        [ (In, TypTypeName (to_p4str_p p "shared_md_t"), "shared_md")
        ; (In, TypTypeName (to_p4str "api_t"), "api")
        ; (InOut, TypTypeName (to_p4str_p p "value_t"), "rw") ]
        ( sub_api_decl @ timekey_reg_decl @ timekey_act_decl @ [timekey_table]
        @ key_decls @ value_reg_decl @ value_act_decl @ [value_table] )
        ( [gen_p4tbl_call "tbl_timekey"]
        @ key_ctrl
        @ [gen_p4tbl_call "tbl_value"] )
    in
    ([], [], [ctrl], key_hash_decls, key_hash_ctrl)

  let get_win_decl (p : string) (alloc : alloc_rec) : prog_tuple =
    let cap_p =
      String.capitalize_ascii (String.sub p 0 (String.length p - 1))
    in
    let prob_base = Z.to_float (z_pow2 num_bit_prob) in
    let prob_list =
      if alloc.num_32b_fp = 0 then list_of_range 1 alloc.r
      else slice_num_acc prob_base alloc.r
    in
    let get_row (i : int) : P4.coq_Declaration =
      DeclInstantiation
        ( noinfo
        , TypSpecializedType
            (TypTypeName (to_p4str (cap_p ^ dsname ^ "Row")), [])
        , [ gen_p4expint
              (if i = 1 then 0 else List.nth prob_list (i - 2))
              num_bit_prob
          ; gen_p4expint (List.nth prob_list (i - 1) - 1) num_bit_prob ]
        , to_p4str ("row_" ^ string_of_int i)
        , [] )
    in
    let rows = map_for_range get_row 1 alloc.r in
    let gen_row_call i : P4.coq_StatementPreT =
      let i = string_of_int i in
      gen_p4tbl_call
        ~args:[["shared_md"]; ["win_md"; "api"]; ["win_md"; "rw_" ^ i]]
        ("row_" ^ i)
    in
    let row_calls = map_for_range gen_row_call 1 alloc.r in
    let ctrl =
      gen_p4ctrl
        (cap_p ^ dsname ^ "Win")
        [ (In, TypTypeName (to_p4str_p p "shared_md_t"), "shared_md")
        ; (InOut, TypTypeName (to_p4str_p p "win_md_t"), "win_md") ]
        rows row_calls
    in
    let get_col (s : string) : P4.coq_Declaration =
      DeclInstantiation
        ( noinfo
        , TypSpecializedType
            (TypTypeName (to_p4str (cap_p ^ dsname ^ "Win")), [])
        , []
        , to_p4str s
        , [] )
    in
    let col_names =
      map_for_range (fun i -> "win_" ^ string_of_int i) 1 alloc.w
    in
    let cols = List.map get_col col_names in
    let col_calls =
      List.map2
        (fun i name ->
          gen_p4tbl_call
            ~args:[["ds_md"; "shared"]; ["ds_md"; "win_" ^ string_of_int i]]
            name )
        (list_of_range 1 alloc.w) col_names
    in
    ([], [], [ctrl], cols, col_calls)

  let gen_reg_decl (p : string)
      (key_poly_salt_list :
        (P4.coq_Declaration * (int * int) option * string) list )
      (num_bit_in_ts : int) (unit_len_log2 : int) (num_unit : Z.t)
      (vname_map : string CidMap.t) (syn : syninfo) (opt : opt_rec)
      (alloc : alloc_rec) : code_type =
    CodeP4
      (union_prog_tuple
         (get_row_decl p key_poly_salt_list num_bit_in_ts unit_len_log2 num_unit
            vname_map syn opt alloc )
         (get_win_decl p alloc) )

  let get_cap_decl (p : string) (num_unit : Z.t) (syn : syninfo)
      (alloc : alloc_rec) : code_type =
    match syn.api_set with
    | ASI ->
        CodeP4 empty_prog_tuple
    | _ ->
        let gen_merge_act ((w, r) : int * int) =
          let w = string_of_int w in
          let r = string_of_int r in
          MkCatAction
            ( "act_merge_win_" ^ w ^ "_row_" ^ r
            , []
            , [ DSAssign
                  ( gen_catname ["query_res"]
                  , gen_catexpdsmd ["win_" ^ w; "rw_" ^ r] ) ] )
        in
        let w_r_list =
          cross_2_lists (list_of_range 1 alloc.w) (list_of_range 1 alloc.r)
        in
        let merge_actions = List.map gen_merge_act w_r_list in
        let name = "tbl_merge_wins" in
        let ks =
          [gen_catexpname ["api"]; gen_catexpdsmd ["shared"; "row_prob"]]
          @ if alloc.w = 1 then [] else [gen_catexpdsmd ["query_window"]]
        in
        let mks =
          ["ternary"; "range"] @ if alloc.w = 1 then [] else ["range"]
        in
        let prob_base = Z.to_float (z_pow2 num_bit_prob) in
        let prob_list =
          if alloc.num_32b_fp = 0 then list_of_range 1 alloc.r
          else slice_num_acc prob_base alloc.r
        in
        let create_entries (key : string) =
          let create_entry ((w, r) : int * int) =
            MkCatEntry
              ( ( [ MIdent (gen_catname [key])
                  ; MMatch
                      (PRange
                         ( ( Z.of_int
                               (if r = 1 then 0 else List.nth prob_list (r - 2))
                           , Some (IConst num_bit_prob) )
                         , ( Z.of_int (List.nth prob_list (r - 1) - 1)
                           , Some (IConst num_bit_prob) ) ) ) ]
                @
                if alloc.w = 1 then []
                else
                  [ MMatch
                      (PRange
                         ( ( Z.( * ) (Z.of_int (w - 1)) num_unit
                           , Some (IConst num_bit_window_t) )
                         , ( Z.( - ) (Z.( * ) (Z.of_int w) num_unit) Z.one
                           , Some (IConst num_bit_window_t) ) ) ) ] )
              , "act_merge_win_" ^ string_of_int w ^ "_row_" ^ string_of_int r
              , [] )
          in
          List.map create_entry w_r_list
        in
        let centries_insquery = create_entries "INSQUERY" in
        let centries_query = create_entries "QUERY" in
        let centries =
          let win_entries =
            match syn.api_set with
            | ASQ | ASIQ ->
                centries_query
            | ASI ->
                []
            | ASInQ | ASIInQ ->
                centries_insquery
            | ASQInQ | ASIQInQ ->
                centries_query @ centries_insquery
          in
          win_entries @ [cat_act_dft (List.length ks)]
        in
        let ctable = MkCatTable (name, ks, mks, centries) in
        CodeTable (ctable, merge_actions)

  let get_res_nodes_and_p4 (p : string) (stage_hash : int) (stage_action : int)
      (max_hash_per_table : int) (min_bit_per_hash : int) (num_bit_in_ts : int)
      (max_idx_per_phv : int) (num_unit : Z.t) (unit_len_log2 : int)
      (var : Cid.t) (atomize : bool) (syn : syninfo) (opt : opt_rec)
      (alloc : alloc_rec) : (res_node list * code_type) list =
    let key_node, hash_nodes, clear_node, api_node, reg_node, cap_node =
      get_res_nodes_in_tup stage_hash stage_action max_hash_per_table
        min_bit_per_hash num_bit_in_ts max_idx_per_phv num_unit unit_len_log2
        atomize syn opt alloc
    in
    let type_decl = get_type_decl p num_bit_per_slot syn alloc in
    let pre_tup =
      [([], type_decl)]
      @ [([], get_ds_metadata_decl p opt alloc)]
      @ [([], get_metadata_fields p alloc)]
    in
    let vname_map = gen_vname_map syn.query_fun in
    let value_tup = [([], get_vname_decl p opt)] in
    let key_tup = [(key_node, get_key_decl p vname_map syn opt)] in
    let start_tup = [([], get_ds_start p dsname opt)] in
    let end_tup = [([], get_ds_end p dsname var syn opt)] in
    let ds_md_tup = [([], get_ds_md p)] in
    let abbr =
      let w_log_2 = int_log2up alloc.w in
      if alloc.w = 1 then Some w_log_2
      else if
        num_unit = Z.one
        && alloc.w land (alloc.w - 1) = 0
        && unit_len_log2 + w_log_2 <= num_bit_in_ts
      then Some w_log_2
      else None
    in
    let index_crc_bit =
      if alloc.num_slot_log2 <= 8 then 8
      else if alloc.num_slot_log2 <= 16 then 16
      else if alloc.num_slot_log2 <= 32 then 32
      else raise (Error "[Bug] Number of slots exceeding the hashing capacity.")
    in
    let prob_crc_bit =
      if List.mem num_bit_prob [8; 16; 32] then num_bit_prob
      else
        raise (Error "[Bug] Number of bits in probability must be 8, 16, or 32.")
    in
    let key_crc_bit = num_bit_timekey in
    let num_32b_key = int_cdiv opt.key_length num_bit_timekey in
    let names_8, names_16, names_32 =
      List.fold_left
        (fun (names_8, names_16, names_32) (k, v) ->
          if k = 8 then (names_8 @ v, names_16, names_32)
          else if k = 16 then (names_8, names_16 @ v, names_32)
          else (names_8, names_16, names_32 @ v) )
        ([], [], [])
        [ (index_crc_bit, if alloc.num_32b_fp = 0 then [] else ["poly_idx"])
        ; (prob_crc_bit, if alloc.num_32b_fp = 0 then [] else ["poly_prob"])
        ; ( key_crc_bit
          , if alloc.num_32b_fp = 0 || alloc.num_32b_fp = num_32b_key then []
            else
              map_for_range
                (fun key -> "poly_key_" ^ string_of_int key)
                1 alloc.num_32b_fp ) ]
    in
    let polysalts_8 = gen_p4hashes 8 names_8 in
    let polysalts_16 = gen_p4hashes 16 names_16 in
    let polysalts_32 = gen_p4hashes 32 names_32 in
    let get_polysalts (crc_num_bit : int) =
      match crc_num_bit with
      | 8 ->
          polysalts_8
      | 16 ->
          polysalts_16
      | 32 ->
          polysalts_32
      | _ ->
          raise (Error "[Bug] Number of bits in hash must be 8, 16, or 32.")
    in
    let look_up_by_prefix (prefix : string) (crc_num_bit : int) =
      let look_up_by_prefix' (decl, salt, name) =
        (* Hacky *)
        if String.sub name 0 (String.length prefix) = prefix then
          [(decl, salt, name)]
        else []
      in
      List.map look_up_by_prefix' (get_polysalts crc_num_bit) |> List.flatten
    in
    let index_poly_salt =
      if alloc.num_32b_fp = 0 then None
      else Some (List.hd (look_up_by_prefix "poly_idx" index_crc_bit))
    in
    let prob_poly_salt =
      if alloc.num_32b_fp = 0 then None
      else Some (List.hd (look_up_by_prefix "poly_pro" prob_crc_bit))
    in
    let key_poly_salt_list =
      if alloc.num_32b_fp = 0 || alloc.num_32b_fp = num_32b_key then []
      else look_up_by_prefix "poly_key" key_crc_bit
    in
    let hash_tup =
      [ ( hash_nodes
        , get_hash_decl p abbr index_poly_salt prob_poly_salt index_crc_bit
            prob_crc_bit unit_len_log2 num_unit num_bit_in_ts opt alloc ) ]
    in
    let clear_tup =
      [ ( clear_node
        , get_clear_decl abbr unit_len_log2 num_unit num_bit_in_ts alloc ) ]
    in
    let api_tup = [(api_node, get_api_decl p num_unit syn alloc)] in
    let reg_tup =
      [ ( reg_node
        , gen_reg_decl p key_poly_salt_list num_bit_in_ts unit_len_log2 num_unit
            vname_map syn opt alloc ) ]
    in
    let cap_decl = get_cap_decl p num_unit syn alloc in
    let cap_tup = [(cap_node, cap_decl)] in
    value_tup @ key_tup @ start_tup @ pre_tup @ ds_md_tup @ hash_tup @ clear_tup
    @ api_tup @ reg_tup @ cap_tup @ end_tup
end
