open SyntaxUtils
open MiscUtils
open DataStructIR
open DataStructUtils
open DataStructShared
open P4IR
open TransUtils
open Collections

module Bloom :
  DS with type opt_rec = sketch_opt_rec and type alloc_rec = sketch_alloc_rec =
struct
  type opt_rec = sketch_opt_rec

  type alloc_rec = sketch_alloc_rec

  let num_bit_per_slot = 8

  let dsname = "BloomFilter"

  let get_alloc (reg_pairs : (int * int) list) : allocinfo list =
    List.map
      (fun (w, r) -> AllocBloom {w; r; block= 0; num_slot_log2= 0})
      reg_pairs

  let add_block (bs_list : (int * int) list) (_ : opt_rec) (alloc : alloc_rec) :
      allocinfo list =
    let add_block' (block, num_slot_log2) =
      AllocBloom {alloc with block; num_slot_log2}
    in
    List.map add_block' bs_list

  let get_block_slot_pairs (opt : opt_rec) : int -> int -> (int * int) list =
    get_block_slot_pairs true num_bit_per_slot opt.num_dist_keys

  (* Bloom's FPR:
     num_slots = num_block * num_bit_per_block / ds_info["bits_per_slot"]
     return 1-(1-(1-(1-1/num_slots)**(input_dist["num_dist_items"]/w))**r)**w *)
  let get_utility (w_pure_int : int) (time_hi : Z.t) (id : int) (syn : syninfo)
      (opt : opt_rec) (alloc : alloc_rec) (input_spec_map : input_map) : float =
    let search_key = string_of_int id ^ "/dist_count" in
    let target_time, hkey_dist_count_target =
      try StrMap.find input_spec_map search_key
      with Not_found ->
        raise
          (Error
             (Printf.sprintf
                "[InputSpec] The required input specification %s not providied"
                search_key ) )
    in
    let hkey_dist_count =
      F.mul
        (F.div hkey_dist_count_target (Z.to_float target_time))
        (Z.to_float time_hi)
    in
    let w_pure = float_of_int w_pure_int in
    let r = float_of_int alloc.r in
    let num_slot = float_of_int (int_pow2 alloc.num_slot_log2) in
    let du =
      (* F.pow
         (F.sub 1.
            (F.pow
               (F.sub 1. (F.div 1. num_slot))
               (F.div hkey_dist_count w_pure) ) )
         r *)
      F.sub 1.
        (F.pow
           (F.sub 1.
              (F.pow
                 (F.sub 1.
                    (F.pow
                       (F.sub 1. (F.div 1. num_slot))
                       (F.div hkey_dist_count w_pure) ) )
                 r ) )
           w_pure )
    in
    du
  (* F.mul opt.qweight du *)

  let dist_idxs (r : int) (w : int) (max_idx : int) : (int * int) list =
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
    else dist_wins r

  let get_res_nodes :
         int
      -> int
      -> int
      -> int
      -> int
      -> int
      -> Z.t
      -> int
      -> bool
      -> syninfo
      -> opt_rec
      -> alloc_rec
      -> res_node list =
    get_res_nodes false

  let get_row_decl (p : string) (syn : syninfo) (alloc : alloc_rec) : prog_tuple
      =
    let reg_decl : P4.coq_Declaration list =
      [ DeclInstantiation
          ( noinfo
          , TypSpecializedType
              ( TypTypeName (to_p4str "Register")
              , [ TypTypeName (to_p4str_p p "value_t")
                ; TypTypeName (to_p4str_p p "index_t") ] )
          , [ gen_p4expint (int_pow2 alloc.num_slot_log2) num_bit_reg_size_t
            ; gen_p4expint 0 num_bit_per_slot ]
          , to_p4str "reg_row"
          , [] ) ]
    in
    let get_reg_pair (name : string) (reg_body : P4.coq_StatementPreT list) :
        P4.coq_Declaration list =
      [ DeclInstantiation
          ( noinfo
          , TypSpecializedType
              ( TypTypeName (to_p4str "RegisterAction")
              , [ TypTypeName (to_p4str_p p "value_t")
                ; TypTypeName (to_p4str_p p "index_t")
                ; TypTypeName (to_p4str_p p "value_t") ] )
          , [gen_p4expname ["reg_row"]]
          , to_p4str ("regact_" ^ name)
          , [ DeclFunction
                ( noinfo
                , TypVoid
                , to_p4str "apply"
                , []
                , [ gen_p4param InOut
                      (TypTypeName (to_p4str_p p "value_t"))
                      "value"
                  ; gen_p4param Out (TypTypeName (to_p4str_p p "value_t")) "rv"
                  ]
                , prestmt_list_to_block reg_body ) ] )
      ; gen_p4act ("act_" ^ name)
          [ StatAssignment
              ( gen_p4expname ["rw"]
              , gen_p4expr
                  (ExpFunctionCall
                     ( gen_p4expname ["regact_" ^ name; "execute"]
                     , []
                     , [Some (gen_p4expname ["index"])] ) ) ) ] ]
    in
    let insert_reg_pair =
      get_reg_pair "insert"
        [ StatAssignment
            (gen_p4expname ["value"], gen_p4expint 1 num_bit_per_slot)
        ; StatAssignment (gen_p4expname ["rv"], gen_p4expint 1 num_bit_per_slot)
        ]
    in
    let query_reg_pair =
      get_reg_pair "query"
        [StatAssignment (gen_p4expname ["rv"], gen_p4expname ["value"])]
    in
    let clear_reg_pair =
      get_reg_pair "clear"
        [ StatAssignment
            (gen_p4expname ["value"], gen_p4expint 0 num_bit_per_slot)
        ; StatAssignment (gen_p4expname ["rv"], gen_p4expint 0 num_bit_per_slot)
        ]
    in
    let reg_pairs =
      ( match syn.api_set with
      | ASQ ->
          query_reg_pair
      | ASI | ASInQ | ASIInQ ->
          insert_reg_pair
      | ASIQ | ASQInQ | ASIQInQ ->
          insert_reg_pair @ query_reg_pair )
      @ clear_reg_pair
    in
    let name = "tbl_bloom" in
    let ks = [gen_catexpname ["api"]] in
    let mks = ["ternary"] in
    let centry_insert =
      [MkCatEntry ([MIdent (gen_catname ["INSERT"])], "act_insert", [])]
    in
    let centry_query =
      [MkCatEntry ([MIdent (gen_catname ["QUERY"])], "act_query", [])]
    in
    let centry_insquery =
      [MkCatEntry ([MIdent (gen_catname ["INSQUERY"])], "act_insert", [])]
    in
    let centry_clear =
      [MkCatEntry ([MIdent (gen_catname ["CLEAR"])], "act_clear", [])]
    in
    let centries =
      let win_entries =
        match syn.api_set with
        | ASQ ->
            centry_query
        | ASI ->
            centry_insert
        | ASInQ ->
            centry_insquery
        | ASIQ ->
            centry_insert @ centry_query
        | ASIInQ ->
            centry_insert @ centry_insquery
        | ASQInQ ->
            centry_query @ centry_insquery
        | ASIQInQ ->
            centry_insert @ centry_query @ centry_insquery
      in
      win_entries @ centry_clear @ [cat_act_dft (List.length ks)]
    in
    let ctable = MkCatTable (name, ks, mks, centries) in
    let table = trans_table ctable in
    let cap_p =
      String.capitalize_ascii (String.sub p 0 (String.length p - 1))
    in
    let ctrl =
      gen_p4ctrl
        (cap_p ^ dsname ^ "Row")
        [ (In, TypTypeName (to_p4str "api_t"), "api")
        ; (In, TypTypeName (to_p4str_p p "index_t"), "index")
        ; (InOut, TypTypeName (to_p4str_p p "value_t"), "rw") ]
        (reg_decl @ reg_pairs @ [table])
        [gen_p4tbl_call name]
    in
    ([], [], [ctrl], [], [])

  let get_win_decl ?(merge_after_win : bool = true) (p : string)
      (alloc : alloc_rec) (rec_merge : bool) : prog_tuple =
    let cap_p =
      String.capitalize_ascii (String.sub p 0 (String.length p - 1))
    in
    let get_row (i : int) : P4.coq_Declaration =
      DeclInstantiation
        ( noinfo
        , TypSpecializedType
            (TypTypeName (to_p4str (cap_p ^ dsname ^ "Row")), [])
        , []
        , to_p4str ("row_" ^ string_of_int i)
        , [] )
    in
    let rows = map_for_range get_row 1 alloc.r in
    let gen_row_call i : P4.coq_StatementPreT =
      let i = string_of_int i in
      gen_p4tbl_call
        ~args:
          [["win_md"; "api"]; ["win_md"; "index_" ^ i]; ["win_md"; "rw_" ^ i]]
        ("row_" ^ i)
    in
    let row_calls = map_for_range gen_row_call 1 alloc.r in
    let merge_actions, merge_tbls, merge_tbl_call =
      if merge_after_win then ([], [], [])
      else if rec_merge then
        let rec gen_act_body_list (tot : int) : P4.coq_StatementPreT list list =
          let gen_act_stmt (lo : int) (hi : int) : P4.coq_StatementPreT =
            let lo = string_of_int lo in
            let hi = string_of_int hi in
            StatAssignment
              ( gen_p4expname ["win_md"; "rw_" ^ lo]
              , gen_p4expr
                  (ExpBinaryOp
                     ( BitAnd
                     , gen_p4expname ["win_md"; "rw_" ^ lo]
                     , gen_p4expname ["win_md"; "rw_" ^ hi] ) ) )
          in
          if tot = 1 then []
          else
            let curr_act_body =
              map_for_range
                (fun lo -> gen_act_stmt lo ((tot / 2) + lo))
                1 (tot / 2)
            in
            curr_act_body :: gen_act_body_list (int_cdiv tot 2)
        in
        let act_body_list = gen_act_body_list alloc.r in
        let num_acts = List.length act_body_list in
        let act_names =
          map_for_range (fun i -> "act_merge_rows" ^ string_of_int i) 1 num_acts
        in
        let tbl_names =
          map_for_range (fun i -> "act_merge_rows" ^ string_of_int i) 1 num_acts
        in
        ( List.map2 gen_p4act act_names act_body_list
        , List.map2 gen_p4tbl tbl_names act_names
        , List.map gen_p4tbl_call tbl_names )
      else
        let merge_action =
          gen_p4act "act_merge_rows"
            [ StatAssignment
                ( gen_p4expname ["win_md"; "rw_1"]
                , gen_p4expint 0 num_bit_per_slot ) ]
        in
        let name = "tbl_merge_rows" in
        let ks =
          map_for_range
            (fun i -> gen_catexpname ["win_md"; "rw_" ^ string_of_int i])
            1 alloc.r
        in
        let mks = list_repeat alloc.r "ternary" in
        let centries =
          [ MkCatEntry
              ( list_repeat alloc.r
                  (MMatch (PNum (Z.of_int 1, Some (IConst num_bit_per_slot))))
              , "NoAction"
              , [] )
          ; MkCatEntry (list_repeat alloc.r (MMatch PWild), "act_merge_rows", [])
          ]
        in
        let merge_ctable = MkCatTable (name, ks, mks, centries) in
        let merge_tbl = trans_table merge_ctable in
        let merge_tbl_call = gen_p4tbl_call name in
        ([merge_action], [merge_tbl], [merge_tbl_call])
    in
    let ctrl =
      gen_p4ctrl
        (cap_p ^ dsname ^ "Win")
        [(InOut, TypTypeName (to_p4str_p p "win_md_t"), "win_md")]
        (rows @ merge_actions @ merge_tbls)
        (row_calls @ merge_tbl_call)
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
          gen_p4tbl_call ~args:[["ds_md"; "win_" ^ string_of_int i]] name )
        (list_of_range 1 alloc.w) col_names
    in
    ([], [], [ctrl], cols, col_calls)

  let gen_reg_decl (p : string) (syn : syninfo) (alloc : alloc_rec)
      (rec_merge : bool) : code_type =
    CodeP4
      (union_prog_tuple (get_row_decl p syn alloc)
         (get_win_decl p alloc rec_merge) )

  let get_cap_decl ?(merge_after_win : bool = true) (p : string) (syn : syninfo)
      (alloc : alloc_rec) : code_type option =
    let cat_one = gen_catint 1 num_bit_per_slot in
    let cat_zero = gen_catint 0 num_bit_per_slot in
    let actions : P4.coq_Declaration list =
      [ gen_p4act "act_merge_wins"
          [ StatAssignment
              ( gen_p4expname ["query_res"]
              , to_p4expint (fst cat_one) (snd cat_one) ) ]
      ; gen_p4act "act_merge_default"
          [ StatAssignment
              ( gen_p4expname ["query_res"]
              , to_p4expint (fst cat_zero) (snd cat_zero) ) ] ]
    in
    let ks =
      gen_catexpname ["api"]
      ::
      ( if merge_after_win then
          List.map
            (fun (i, j) ->
              gen_catexpdsmd ["win_" ^ string_of_int i; "rw_" ^ string_of_int j]
              )
            (cross_2_lists (list_of_range 1 alloc.w) (list_of_range 1 alloc.r))
        else
          map_for_range
            (fun i -> gen_catexpdsmd ["win_" ^ string_of_int i; "rw_1"])
            1 alloc.w )
    in
    let mks = list_repeat (List.length ks) "ternary" in
    let get_centries (s : string) : cat_entry list =
      let get_centry (one_pos : int) : cat_entry =
        MkCatEntry
          ( ( [MIdent (gen_catname [s])]
            @
            if merge_after_win then
              map_for_range
                (fun i ->
                  if i / alloc.r = one_pos then
                    MMatch (Cat.PNum (fst cat_one, opt_z_to_size (snd cat_one)))
                  else cat_match_dc )
                0
                ((alloc.w * alloc.r) - 1)
            else
              map_for_range
                (fun i ->
                  if i = one_pos then
                    MMatch (Cat.PNum (fst cat_one, opt_z_to_size (snd cat_one)))
                  else cat_match_dc )
                1 alloc.w )
          , "act_merge_wins"
          , [] )
      in
      map_for_range get_centry 0 (alloc.w - 1)
      @ [ MkCatEntry
            ( [MIdent (gen_catname [s])]
              @ list_repeat
                  (if merge_after_win then alloc.w * alloc.r else alloc.w)
                  (MMatch PWild)
            , "act_merge_default"
            , [] ) ]
    in
    let centries_query = get_centries "QUERY" in
    let centries_insquery = get_centries "INSQUERY" in
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
    let name = "tbl_merge_wins" in
    let ctable = MkCatTable (name, ks, mks, centries) in
    let table = trans_table ctable in
    match syn.api_set with
    | ASI ->
        None
    | _ ->
        Some (CodeP4 ([], [], [], actions @ [table], [gen_p4tbl_call name]))

  let get_res_nodes_and_p4 (p : string) (stage_hash : int) (stage_action : int)
      (max_hash_per_table : int) (min_bit_per_hash : int) (num_bit_in_ts : int)
      (max_idx_per_phv : int) (num_unit : Z.t) (unit_len_log2 : int)
      (var : Cid.t) (atomize : bool) (syn : syninfo) (opt : opt_rec)
      (alloc : alloc_rec) : (res_node list * code_type) list =
    let reg_decl = gen_reg_decl p syn alloc false in
    let cap_decl = get_cap_decl p syn alloc in
    get_res_nodes_and_p4 dsname num_bit_per_slot reg_decl cap_decl p stage_hash
      stage_action max_hash_per_table min_bit_per_hash num_bit_in_ts
      max_idx_per_phv num_unit unit_len_log2 var atomize syn opt alloc
end
