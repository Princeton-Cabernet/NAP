open SyntaxUtils
open MiscUtils
open DataStructIR
open DataStructUtils
open SetIR
open P4IR
open TransUtils
module P4Alias = Poulet4.Syntax

(* let dist_idxs (r : int) (w : int) (max_idx : int) : (int * int) list =
   let rec dist_rows (w' : int) : (int * int) list =
     if w' <= max_idx - 2 then [(1, w')]
     else
       let w_to_split = max_idx - 2 in
       (1, w_to_split) :: dist_rows (w' - w_to_split)
   in
   let rec dist_wins (r' : int) : (int * int) list =
     if (r' * (w + 1)) + 1 <= max_idx then [(r', w)]
     else
       let r_to_split = (max_idx - 1) / (w + 1) in
       (r_to_split, w) :: dist_wins (r' - r_to_split)
   in
   if w > max_idx - 2 then list_repeat r (dist_rows w) |> List.flatten
   else dist_wins r *)

(* Assume overlaying *)
let dist_idxs (r : int) (w : int) (max_idx : int) : (int * int) list =
  let rec dist_rows (w' : int) : (int * int) list =
    if w' <= max_idx then [(1, w')]
    else
      let w_to_split = max_idx in
      (1, w_to_split) :: dist_rows (w' - w_to_split)
  in
  let rec dist_wins (r' : int) : (int * int) list =
    if r' * w <= max_idx then [(r', w)]
    else
      let r_to_split = max_idx / w in
      (r_to_split, w) :: dist_wins (r' - r_to_split)
  in
  if w > max_idx then list_repeat r (dist_rows w) |> List.flatten
  else dist_wins r

let get_copy_info (max_idx_per_phv : int) (alloc : sketch_alloc_rec) :
    (int * int) list * int * int =
  let idx_groups = dist_idxs alloc.r alloc.w max_idx_per_phv in
  let hash_copies = max 0 (List.length idx_groups - alloc.r) in
  assert (hash_copies mod alloc.r = 0) ;
  let clear_copies = List.length idx_groups - 1 in
  (idx_groups, hash_copies, clear_copies)

let get_res_nodes_in_tup ?(merge_after_win : bool = true) (rec_merge : bool)
    (stage_hash : int) (stage_action : int) (max_hash_per_table : int)
    (min_bit_per_hash : int) (num_bit_in_ts : int) (max_idx_per_phv : int)
    (num_unit : Z.t) (unit_len_log2 : int) (atomize : bool) (syn : syninfo)
    (opt : sketch_opt_rec) (alloc : sketch_alloc_rec) =
  let key_node =
    [ { typ=
          ( if atomize then Atom (if opt.num_dist_keys > 1 then true else false)
            else Table (if opt.num_dist_keys > 1 then true else false) )
      ; num_tbl= 1
      ; num_act=
          ( (if opt.num_dist_keys > 1 then opt.num_dist_keys else 1)
          + if syn.has_clear_branch then 1 else 0 )
      ; num_hash= 0
      ; num_reg= 0
      ; num_block= 0 } ]
  in
  let _, hash_copies, clear_copies = get_copy_info max_idx_per_phv alloc in
  let num_hash_per_index = int_cdiv alloc.num_slot_log2 min_bit_per_hash in
  if max_hash_per_table / num_hash_per_index = 0 then
    raise
      (Error
         "[Alloc] Unsupported: it requires multiple tables to generate one \
          hash/clear index." ) ;
  let hash_nodes =
    (* There can be better strategies to decide which hash scheme to use *)
    (* let num_hashes =
         alloc.r * int_cdiv alloc.num_slot_log2 min_bit_per_hash
       in
       let num_hashes_1 = opt.num_dist_keys * num_hashes in
       let num_stage_1 = int_cdiv num_hashes_1 stage_hash in
       let num_stage_2 =
         int_cdiv opt.num_dist_keys stage_action
         + int_cdiv num_hashes stage_hash
       in *)
    (* Note 8/21/23: This resource saving seems not reflected in get_hash_decl.
       Commented out for now. *)
    (* if opt.num_dist_keys = 0 then []
       else *)
    let get_hash_nodes (num_tbl : int) =
      let one_hash_node =
        { typ= Hash false
        ; num_tbl= 1
        ; num_act= 1
        ; num_hash= num_hash_per_index
        ; num_reg= 0
        ; num_block= 0 }
      in
      let end_hash_node =
        [ { typ= Hash true
          ; num_tbl= 1
          ; num_act= 1
          ; num_hash= num_hash_per_index
          ; num_reg= 0
          ; num_block= 0 } ]
      in
      list_repeat (num_tbl - 1) one_hash_node @ end_hash_node
    in
    get_hash_nodes (alloc.r + hash_copies)
  in
  let clear_node =
    let get_clear_copies (num_copies : int) =
      let one_clear_copy =
        { typ= Atom false
        ; num_tbl= 1
        ; num_act= 1
        ; num_hash= num_hash_per_index
        ; num_reg= 0
        ; num_block= 0 }
      in
      let end_clear_copy =
        [ { typ= Clear (false, true)
          ; num_tbl= 1
          ; num_act= 1
          ; num_hash= num_hash_per_index
          ; num_reg= 0
          ; num_block= 0 } ]
      in
      if num_copies = 0 then []
      else list_repeat (clear_copies - 1) one_clear_copy @ end_clear_copy
    in
    if
      num_unit = Z.one
      && alloc.w land (alloc.w - 1) = 0
      && unit_len_log2 + int_log2up alloc.w <= num_bit_in_ts
    then
      [ { typ= Clear (true, if clear_copies = 0 then true else false)
        ; num_tbl= 1
        ; num_act= 1
        ; num_hash= 0
        ; num_reg= 1
        ; num_block= 1 } ]
      @ get_clear_copies clear_copies
    else
      [ { typ= Clear (true, false)
        ; num_tbl= 1
        ; num_act= 1 (* Hash unit seems not needed *)
        ; num_hash= 0
        ; num_reg= 1
        ; num_block= 1 }
      ; { typ= Clear (true, if clear_copies = 0 then true else false)
        ; num_tbl= 1
        ; num_act= 2 (* Hash unit seems note needed *)
        ; num_hash= 0
        ; num_reg= 1
        ; num_block= 1 } ]
      @ get_clear_copies clear_copies
  in
  let api_node =
    [ { typ= (if atomize then Atom true else Table true)
      ; num_tbl= 1
      ; num_act= alloc.w
      ; num_hash= 0
      ; num_reg= 0
      ; num_block= 0 } ]
  in
  let reg_node =
    let num_act = opt.num_reg_progs + 1 in
    let one_reg_node =
      { typ= Reg false
      ; num_tbl=
          (if merge_after_win then 1 else if rec_merge then alloc.r else 2)
      ; num_act
      ; num_hash= num_hash_per_index
      ; num_reg= alloc.r
      ; num_block= alloc.block }
    in
    let end_reg_node =
      [ { typ= Reg true
        ; num_tbl=
            (if merge_after_win then 1 else if rec_merge then alloc.r else 2)
        ; num_act
        ; num_hash= num_hash_per_index
        ; num_reg= alloc.r
        ; num_block= alloc.block } ]
    in
    list_repeat (alloc.w - 1) one_reg_node @ end_reg_node
  in
  let cap_node =
    match syn.api_set with
    | ASI ->
        []
    | _ ->
        let num_cap_node = int_log2up alloc.w in
        let one_cap_node =
          { typ= Atom true
          ; num_tbl= 1
          ; num_act= 1
          ; num_hash= 0
          ; num_reg= 0
          ; num_block= 0 }
        in
        let end_cap_node =
          [ { typ= Atom false
            ; num_tbl= 1
            ; num_act= 2
            ; num_hash= 0
            ; num_reg= 0
            ; num_block= 0 } ]
        in
        if rec_merge then
          list_repeat (num_cap_node - 1) one_cap_node @ end_cap_node
        else end_cap_node
  in
  (key_node, hash_nodes, clear_node, api_node, reg_node, cap_node)

let get_res_nodes (rec_merge : bool) (stage_hash : int) (stage_action : int)
    (max_hash_per_table : int) (min_bit_per_hash : int) (num_bit_in_ts : int)
    (max_idx_per_phv : int) (num_unit : Z.t) (unit_len_log2 : int)
    (atomize : bool) (syn : syninfo) (opt : sketch_opt_rec)
    (alloc : sketch_alloc_rec) : res_node list =
  let key_node, hash_nodes, clear_node, api_node, reg_node, cap_node =
    get_res_nodes_in_tup rec_merge stage_hash stage_action max_hash_per_table
      min_bit_per_hash num_bit_in_ts max_idx_per_phv num_unit unit_len_log2
      atomize syn opt alloc
  in
  key_node @ hash_nodes @ clear_node @ api_node @ reg_node @ cap_node

let get_type_decl (p : string) (num_bit_per_slot : int) (syn : syninfo)
    (alloc : sketch_alloc_rec) : code_type * int =
  let keys_bit_length = numeric_raw_ty_size syn.keys_ty in
  ( CodeP4
      ( [ gen_p4decltypedef (p ^ "index_t") alloc.num_slot_log2
        ; gen_p4decltypedef (p ^ "value_t") num_bit_per_slot
        ; gen_p4decltypedef (p ^ "key_t") keys_bit_length ]
      , []
      , []
      , []
      , [] )
  , keys_bit_length )

let get_ds_metadata_decl (p : string) (hash_copies : int) (clear_copies : int)
    (alloc : sketch_alloc_rec) : code_type =
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
                , TypTypeName (to_p4str_p p "index_t")
                , to_p4str ("index_" ^ string_of_int i) ) )
            1 alloc.r
        @ map_for_range
            (fun i ->
              P4Alias.MkDeclarationField
                ( noinfo
                , TypTypeName (to_p4str_p p "value_t")
                , to_p4str ("rw_" ^ string_of_int i) ) )
            1 alloc.r )
  in
  let ds_md_decl : P4.coq_Declaration =
    DeclStruct
      ( noinfo
      , to_p4str_p p "ds_md_t"
      , [ P4Alias.MkDeclarationField
            (noinfo, TypTypeName (to_p4str "window_t"), to_p4str "clear_window")
        ]
        @ map_for_range
            (fun i ->
              P4Alias.MkDeclarationField
                ( noinfo
                , TypTypeName (to_p4str_p p "index_t")
                , to_p4str ("clear_index_" ^ string_of_int i) ) )
            1 (1 + clear_copies)
        @ map_for_range
            (fun i ->
              P4Alias.MkDeclarationField
                ( noinfo
                , TypTypeName (to_p4str_p p "index_t")
                , to_p4str ("hash_index_" ^ string_of_int i) ) )
            1 (alloc.r + hash_copies)
        @ map_for_range
            (fun i ->
              P4Alias.MkDeclarationField
                ( noinfo
                , TypTypeName (to_p4str_p p "win_md_t")
                , to_p4str ("win_" ^ string_of_int i) ) )
            1 alloc.w )
  in
  CodeP4 ([win_md_decl; ds_md_decl], [], [], [], [])

let get_metadata_fields (p : string) (alloc : sketch_alloc_rec) : code_type =
  let meta_fields : P4.coq_DeclarationField list =
    [ MkDeclarationField
        (noinfo, TypTypeName (to_p4str_p p "key_t"), to_p4str_p p "key")
    ; MkDeclarationField
        (noinfo, TypTypeName (to_p4str "api_t"), to_p4str_p p "api") ]
  in
  CodeP4 ([], meta_fields, [], [], [])

let gen_p4dsmd (ss : string list) = gen_p4expname ("ds_md" :: ss)

let gen_catdsmd (ss : string list) = gen_catname ("ds_md" :: ss)

let gen_catexpdsmd (ss : string list) : Cat.exp =
  gen_catexpr (EVar (gen_catdsmd ss))

let get_key_decl (p : string) (syn : syninfo) (opt : sketch_opt_rec) : code_type
    =
  let fill_in_entry (keys_ids_list : (Cat.e list * int) list)
      ((pats, api, keys) : set_branch) : cat_entry =
    let matches = List.map (fun m -> MMatch m) pats in
    let action_name =
      match api with
      | AClear ->
          p ^ "act_set_clear_key"
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
      , DSAssign (gen_catmeta [p ^ "api"], gen_catexpname ["api"])
        ::
        ( if opt.num_dist_keys > 1 then
            [DSAssign (gen_catmeta [p ^ "key"], snd (concat_keys keys))]
          else [] ) )
  in
  let keys_list =
    list_uniq (List.map (fun (_, _, keys) -> keys) syn.branches)
  in
  let ids = list_of_range 1 (List.length keys_list) in
  let keys_ids_list = List.combine keys_list ids in
  let key_actions = List.map create_key_action keys_ids_list in
  let clear_key_action =
    [ MkCatAction
        ( p ^ "act_set_clear_key"
        , []
        , [DSAssign (gen_catmeta [p ^ "api"], gen_catexpname ["CLEAR"])] ) ]
  in
  let cactions =
    key_actions @ if syn.has_clear_branch then clear_key_action else []
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

let get_ds_start (p : string) (dsname : string) : code_type =
  let cap_p = String.capitalize_ascii (String.sub p 0 (String.length p - 1)) in
  let ds_name = cap_p ^ dsname in
  let args : param_tuple list =
    [ (In, TypTypeName (to_p4str_p p "key_t"), "ds_key")
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
          (noinfo, TypTypeName (to_p4str_p p "ds_md_t"), to_p4str "ds_md", None)
      ]
    , [] )

let get_ds_end (p : string) (dsname : string) (keys_bit_length : int)
    (var : Cid.t) (syn : syninfo) (opt : sketch_opt_rec) : code_type =
  let cap_p = String.capitalize_ascii (String.sub p 0 (String.length p - 1)) in
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
      if opt.num_dist_keys = 0 then [Some (gen_p4expint 0 keys_bit_length)]
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
      str_to_exp [["ig_md"; p ^ "api"]; ["ig_intr_md"; "ingress_mac_tstamp"]]
    in
    StatMethodCall
      ( gen_p4expname [instance_name; "apply"]
      , []
      , key @ in_args @ [Some (trans_ident var)] )
  in
  CodeCtrlEnd ([], [], [], [instance], [instance_call])

let get_clear_decl (abbr : int option) (unit_len_log2 : int) (num_unit : Z.t)
    (num_bit_in_ts : int) (clear_copies : int) (alloc : sketch_alloc_rec) :
    code_type =
  let clear_index_decls : P4.coq_Declaration list =
    [ DeclInstantiation
        ( noinfo
        , TypSpecializedType
            ( TypTypeName (to_p4str "Register")
            , [ TypBit (Bigint.of_int max_bit_index)
              ; TypBit (Bigint.of_int num_bit_clear_index) ] )
        , [gen_p4expint 1 num_bit_reg_size_t; gen_p4expint 0 max_bit_index]
        , to_p4str "reg_clear_index"
        , [] )
    ; DeclInstantiation
        ( noinfo
        , TypSpecializedType
            ( TypTypeName (to_p4str "RegisterAction")
            , [ TypBit (Bigint.of_int max_bit_index)
              ; TypBit (Bigint.of_int num_bit_clear_index)
              ; TypBit (Bigint.of_int max_bit_index) ] )
        , [gen_p4expname ["reg_clear_index"]]
        , to_p4str "regact_clear_index"
        , [ DeclFunction
              ( noinfo
              , TypVoid
              , to_p4str "apply"
              , []
              , [ gen_p4param InOut (TypBit (Bigint.of_int max_bit_index)) "val"
                ; gen_p4param Out (TypBit (Bigint.of_int max_bit_index)) "rv" ]
              , prestmt_list_to_block
                  [ StatAssignment (gen_p4expname ["rv"], gen_p4expname ["val"])
                  ; StatAssignment
                      ( gen_p4expname ["val"]
                      , gen_p4expr
                          (ExpBinaryOp
                             ( Plus
                             , gen_p4expname ["val"]
                             , gen_p4expint 1 max_bit_index ) ) ) ] ) ] ) ]
  in
  let crc_num_bit =
    if alloc.num_slot_log2 <= 8 then 8
    else if alloc.num_slot_log2 <= 16 then 16
    else if alloc.num_slot_log2 <= 32 then 32
    else raise (Error "[Bug] Number of slots exceeding the hashing capacity.")
  in
  let get_copy_pair (id : int) : P4.coq_Declaration list =
    let id = string_of_int id in
    [ DeclInstantiation
        ( noinfo
        , TypSpecializedType
            (TypTypeName (to_p4str "Hash"), [TypBit (Bigint.of_int crc_num_bit)])
        , [gen_p4expname ["HashAlgorithm_t"; "IDENTITY"]]
        , to_p4str ("copy_clear_" ^ id)
        , [] )
    ; gen_p4act ("act_copy_clear_" ^ id)
        [ StatAssignment
            ( gen_p4dsmd ["clear_index_" ^ id]
            , gen_p4expr
                (ExpBitStringAccess
                   ( gen_p4expr
                       (ExpFunctionCall
                          ( gen_p4expname ["copy_clear_" ^ id; "get"]
                          , []
                          , [Some (gen_p4dsmd ["clear_index_1"])] ) )
                   , Bigint.zero
                   , Bigint.of_int (alloc.num_slot_log2 - 1) ) ) ) ]
    ; gen_p4tbl ("tbl_copy_clear_" ^ id) ("act_copy_clear_" ^ id) ]
  in
  let copy_decls =
    map_for_range get_copy_pair 2 (clear_copies + 1) |> List.flatten
  in
  let copy_ctrl =
    map_for_range
      (fun i -> gen_p4tbl_call ("tbl_copy_clear_" ^ string_of_int i))
      2 (clear_copies + 1)
  in
  match abbr with
  | Some w_log_2 ->
      let clear_decls =
        clear_index_decls
        @ [ gen_p4act "act_clear_index"
              [ StatAssignment
                  ( gen_p4dsmd ["clear_index_1"]
                  , gen_p4expr
                      (ExpBitStringAccess
                         ( gen_p4expr
                             (ExpFunctionCall
                                ( gen_p4expname ["regact_clear_index"; "execute"]
                                , []
                                , [Some (gen_p4expint 0 num_bit_clear_index)] )
                             )
                         , Bigint.zero
                         , Bigint.of_int (alloc.num_slot_log2 - 1) ) ) )
                (* Untested yet *)
                (* w_log_2 >= 1 *)
              ; StatAssignment
                  ( gen_p4dsmd ["clear_window"]
                  , gen_p4expr
                      (ExpCast
                         ( TypTypeName (to_p4str "window_t")
                         , gen_p4expr
                             (ExpBitStringAccess
                                ( gen_p4expname ["ingress_mac_tstamp"]
                                , Bigint.of_int unit_len_log2
                                , Bigint.of_int (unit_len_log2 + w_log_2 - 1) )
                             ) ) ) ) ]
          ; gen_p4tbl "tbl_clear_index" "act_clear_index" ]
      in
      let ig_ctrl = [gen_p4tbl_call "tbl_clear_index"] in
      CodeP4 ([], [], [], clear_decls @ copy_decls, ig_ctrl @ copy_ctrl)
  | None ->
      let ig_decls =
        clear_index_decls
        @ [ gen_p4act "act_clear_index"
              [ StatAssignment
                  ( gen_p4dsmd ["clear_index_1"]
                  , gen_p4expr
                      (ExpBitStringAccess
                         ( gen_p4expr
                             (ExpFunctionCall
                                ( gen_p4expname ["regact_clear_index"; "execute"]
                                , []
                                , [Some (gen_p4expint 0 num_bit_clear_index)] )
                             )
                         , Bigint.zero
                         , Bigint.of_int (alloc.num_slot_log2 - 1) ) ) ) ]
          ; gen_p4tbl "tbl_clear_index" "act_clear_index"
          ; DeclInstantiation
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
              , to_p4str "reg_clear_window"
              , [] )
          ; DeclInstantiation
              ( noinfo
              , TypSpecializedType
                  ( TypTypeName (to_p4str "RegisterAction")
                  , [ TypTypeName (to_p4str "window_pair_t")
                    ; TypBit (Bigint.of_int num_bit_clear_index)
                    ; TypTypeName (to_p4str "window_t") ] )
              , [gen_p4expname ["reg_clear_window"]]
              , to_p4str "regact_clear_window_signal_0"
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
              , [gen_p4expname ["reg_clear_window"]]
              , to_p4str "regact_clear_window_signal_1"
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
          ; gen_p4act "act_clear_window_signal_0"
              [ StatAssignment
                  ( gen_p4dsmd ["clear_window"]
                  , gen_p4expr
                      (ExpFunctionCall
                         ( gen_p4expname
                             ["regact_clear_window_signal_0"; "execute"]
                         , []
                         , [Some (gen_p4expint 0 num_bit_clear_index)] ) ) ) ]
          ; gen_p4act "act_clear_window_signal_1"
              [ StatAssignment
                  ( gen_p4dsmd ["clear_window"]
                  , gen_p4expr
                      (ExpFunctionCall
                         ( gen_p4expname
                             ["regact_clear_window_signal_1"; "execute"]
                         , []
                         , [Some (gen_p4expint 0 num_bit_clear_index)] ) ) ) ]
          ; DeclTable
              ( noinfo
              , to_p4str "tbl_clear_window"
              , [ MkTableKey
                    ( noinfo
                    , gen_p4expname ["ingress_mac_tstamp"]
                    , to_p4str "ternary" ) ]
              , [ gen_p4actref_na "act_clear_window_signal_0"
                ; gen_p4actref_na "act_clear_window_signal_1" ]
              , Some
                  [ gen_p4entry_na
                      [ MatchMask
                          ( gen_p4expint 0 num_bit_in_ts
                          , gen_p4expint
                              (int_pow2 (unit_len_log2 - 1))
                              num_bit_in_ts ) ]
                      "act_clear_window_signal_0"
                  ; gen_p4entry_na [MatchDontCare] "act_clear_window_signal_1"
                  ]
              , Some (gen_p4actref_na "act_clear_window_signal_1")
              , Some (Bigint.of_int 2)
              , [] ) ]
      in
      let ig_ctrl =
        [gen_p4tbl_call "tbl_clear_index"; gen_p4tbl_call "tbl_clear_window"]
      in
      CodeP4 ([], [], [], ig_decls @ copy_decls, ig_ctrl @ copy_ctrl)

let get_hash_decl (p : string) (hash_copies : int) (opt : sketch_opt_rec)
    (alloc : sketch_alloc_rec) : code_type =
  let crc_num_bit =
    if alloc.num_slot_log2 <= 8 then 8
    else if alloc.num_slot_log2 <= 16 then 16
    else if alloc.num_slot_log2 <= 32 then 32
    else raise (Error "[Bug] Number of slots exceeding the hashing capacity.")
  in
  (*ATTN: hash_copies would matter in the polynomial picked
    e.g. a list of polynomials and chosen by index at id mod alloc.r
  *)
  let get_hash_pair (hash_input : P4.coq_Expression)
      ((poly_decl, salt, _) : P4.coq_Declaration * (int * int) option * string)
      (id : int) : P4.coq_Declaration list =
    let id = string_of_int id in
    [ poly_decl
    ; DeclInstantiation
        ( noinfo
        , TypSpecializedType
            (TypTypeName (to_p4str "Hash"), [TypBit (Bigint.of_int crc_num_bit)])
        , [ gen_p4expname ["HashAlgorithm_t"; "CUSTOM"]
          ; gen_p4expname ["poly_idx_" ^ id] ]
        , to_p4str ("hash_idx_" ^ id)
        , [] )
    ; gen_p4act ("act_hash_index_" ^ id)
        [ StatAssignment
            ( gen_p4dsmd ["hash_index_" ^ id]
            , gen_p4expr
                (ExpBitStringAccess
                   ( gen_p4expr
                       (ExpFunctionCall
                          ( gen_p4expname ["hash_idx_" ^ id; "get"]
                          , []
                          , [ Some
                                ( match salt with
                                | None ->
                                    hash_input
                                | Some (v, w) ->
                                    gen_p4expr
                                      (ExpBinaryOp
                                         (PlusPlus, hash_input, gen_p4expint v w)
                                      ) ) ] ) )
                   , Bigint.zero
                   , Bigint.of_int (alloc.num_slot_log2 - 1) ) ) ) ]
    ; gen_p4tbl ("tbl_hash_index_" ^ id) ("act_hash_index_" ^ id) ]
  in
  let tot_hashes = hash_copies + alloc.r in
  let poly_names =
    map_for_range (fun id -> "poly_idx_" ^ string_of_int id) 1 tot_hashes
  in
  let hash_salt_list = gen_p4hashes crc_num_bit poly_names in
  let ig_decls =
    map_for_range
      (fun i ->
        get_hash_pair (gen_p4expname ["ds_key"])
          (List.nth hash_salt_list (i - 1))
          i )
      1 tot_hashes
    |> List.flatten
  in
  let ig_ctrl =
    map_for_range
      (fun id -> gen_p4tbl_call ("tbl_hash_index_" ^ string_of_int id))
      1 tot_hashes
  in
  CodeP4 ([], [], [], ig_decls, ig_ctrl)

let get_api_decl (p : string) (num_unit : Z.t) (idx_groups : (int * int) list)
    (syn : syninfo) (alloc : sketch_alloc_rec) : code_type =
  let idxs_split_w () =
    let hash_sets = List.length idx_groups / alloc.r in
    let one_hash_set = fst (split_after_nth idx_groups (hash_sets - 1)) in
    map_for_range
      (fun i ->
        list_repeat
          (snd (List.nth one_hash_set i))
          (list_of_range ((i * alloc.r) + 1) ((i + 1) * alloc.r))
        |> List.flatten )
      0 (hash_sets - 1)
    |> List.flatten
  in
  let clear_idxs =
    if List.length idx_groups <= alloc.r then
      list_repeat alloc.w
        ( map_for_range
            (fun i -> list_repeat (fst (List.nth idx_groups i)) (i + 1))
            0
            (List.length idx_groups - 1)
        |> List.flatten )
      |> List.flatten
    else idxs_split_w ()
  in
  let hash_idxs =
    (* i.e. w <= max_idx - 2 *)
    if List.length idx_groups <= alloc.r then
      list_repeat alloc.w (list_of_range 1 alloc.r) |> List.flatten
    else idxs_split_w ()
  in
  let create_api_action (clear_win : int) : cat_action =
    let assign_win_index ((curr_win, curr_row) : int * int) : Cat.dag_stmt =
      let idx = ((curr_win - 1) * alloc.r) + curr_row - 1 in
      DSAssign
        ( gen_catdsmd
            ["win_" ^ string_of_int curr_win; "index_" ^ string_of_int curr_row]
        , gen_catexpdsmd
            [ ( if curr_win = clear_win then
                  "clear_index_" ^ string_of_int (List.nth clear_idxs idx)
                else "hash_index_" ^ string_of_int (List.nth hash_idxs idx) ) ]
        )
    in
    let assign_win_api (curr_win : int) : Cat.dag_stmt =
      let curr_win = string_of_int curr_win in
      DSAssign
        ( gen_catdsmd ["win_" ^ curr_win; "api"]
        , gen_catexpname ["api_" ^ curr_win] )
    in
    let param_pairs =
      cross_2_lists (list_of_range 1 alloc.w) (list_of_range 1 alloc.r)
    in
    let action_body =
      List.map assign_win_index param_pairs
      @ map_for_range assign_win_api 1 alloc.w
    in
    let params =
      map_for_range
        (fun i ->
          (Cat.ty (Cat.TInt (IConst num_bit_api_call)), "api_" ^ string_of_int i)
          )
        1 alloc.w
    in
    MkCatAction
      ("act_set_clear_win_" ^ string_of_int clear_win, params, action_body)
  in
  let cactions = map_for_range create_api_action 1 alloc.w in
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
        , "act_set_clear_win_" ^ string_of_int clear_win
        , map_for_range (gen_act_args (clear_win - 1)) 0 (alloc.w - 1) )
    in
    map_for_range create_entry 1 alloc.w
  in
  let centries_insert =
    let gen_act_args (clear_win : int) (i : int) =
      if i = clear_win then gen_catexpname ["CLEAR"]
      else if i = (clear_win - 1 + alloc.w) mod alloc.w then
        gen_catexpname ["INSERT"]
      else gen_catexpname ["NOOP"]
    in
    create_entries "INSERT" gen_act_args
  in
  let centries_query =
    match syn.time_fun with
    | TLast _ ->
        let gen_act_args (clear_win : int) (i : int) =
          if i = clear_win then gen_catexpname ["CLEAR"]
          else if i = (clear_win - 1 + alloc.w) mod alloc.w then
            gen_catexpname ["NOOP"]
          else gen_catexpname ["QUERY"]
        in
        create_entries "QUERY" gen_act_args
    | _ ->
        let gen_act_args (clear_win : int) (i : int) =
          if i = clear_win then gen_catexpname ["CLEAR"]
          else gen_catexpname ["QUERY"]
        in
        create_entries "QUERY" gen_act_args
  in
  let centries_insquery =
    match syn.time_fun with
    | TLast _ ->
        let gen_act_args (clear_win : int) (i : int) =
          if i = clear_win then gen_catexpname ["CLEAR"]
          else if i = (clear_win - 1 + alloc.w) mod alloc.w then
            gen_catexpname ["INSERT"]
          else gen_catexpname ["QUERY"]
        in
        create_entries "INSQUERY" gen_act_args
    | _ ->
        let gen_act_args (clear_win : int) (i : int) =
          if i = clear_win then gen_catexpname ["CLEAR"]
          else if i = (clear_win - 1 + alloc.w) mod alloc.w then
            gen_catexpname ["INSQUERY"]
          else gen_catexpname ["QUERY"]
        in
        create_entries "INSQUERY" gen_act_args
  in
  let centries_clear =
    let gen_act_args (clear_win : int) (i : int) =
      if i = clear_win then gen_catexpname ["CLEAR"] else gen_catexpname ["NOOP"]
    in
    create_entries "CLEAR" gen_act_args
  in
  let ks = [gen_catexpname ["api"]; gen_catexpdsmd ["clear_window"]] in
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
    @ (if syn.has_clear_branch then centries_clear else [])
    @ [cat_act_dft (List.length ks)]
  in
  let ctable = MkCatTable ("tbl_set_win", ks, mks, centries) in
  CodeTable (ctable, cactions)

let get_res_nodes_and_p4 (dsname : string) (num_bit_per_slot : int)
    (reg_decl : code_type) (cap_decl : code_type option) (p : string)
    (stage_hash : int) (stage_action : int) (max_hash_per_table : int)
    (min_bit_per_hash : int) (num_bit_in_ts : int) (max_idx_per_phv : int)
    (num_unit : Z.t) (unit_len_log2 : int) (var : Cid.t) (atomize : bool)
    (syn : syninfo) (opt : sketch_opt_rec) (alloc : sketch_alloc_rec) :
    (res_node list * code_type) list =
  let key_node, hash_nodes, clear_node, api_node, reg_node, cap_node =
    get_res_nodes_in_tup false stage_hash stage_action max_hash_per_table
      min_bit_per_hash num_bit_in_ts max_idx_per_phv num_unit unit_len_log2
      atomize syn opt alloc
  in
  let idx_groups, hash_copies, clear_copies =
    get_copy_info max_idx_per_phv alloc
  in
  let type_decl, keys_bit_length = get_type_decl p num_bit_per_slot syn alloc in
  let pre_tup =
    [([], type_decl)]
    @ [([], get_ds_metadata_decl p hash_copies clear_copies alloc)]
    @ [([], get_metadata_fields p alloc)]
  in
  let key_tup = [(key_node, get_key_decl p syn opt)] in
  let start_tup = [([], get_ds_start p dsname)] in
  let end_tup = [([], get_ds_end p dsname keys_bit_length var syn opt)] in
  let ds_md_tup = [([], get_ds_md p)] in
  let hash_tup = [(hash_nodes, get_hash_decl p hash_copies opt alloc)] in
  let clear_tup =
    let w_log_2 = int_log2up alloc.w in
    if
      num_unit = Z.one
      && alloc.w land (alloc.w - 1) = 0
      && unit_len_log2 + w_log_2 <= num_bit_in_ts
    then
      [ ( clear_node
        , get_clear_decl (Some w_log_2) unit_len_log2 num_unit num_bit_in_ts
            clear_copies alloc ) ]
    else
      [ ( clear_node
        , get_clear_decl None unit_len_log2 num_unit num_bit_in_ts clear_copies
            alloc ) ]
  in
  let api_tup = [(api_node, get_api_decl p num_unit idx_groups syn alloc)] in
  let reg_tup = [(reg_node, reg_decl)] in
  let cap_tup =
    match cap_decl with None -> [] | Some cap_decl -> [(cap_node, cap_decl)]
  in
  key_tup @ start_tup @ pre_tup @ ds_md_tup @ hash_tup @ clear_tup @ api_tup
  @ reg_tup @ cap_tup @ end_tup
