open SyntaxUtils
open MiscUtils
open DataStructIR
open DataStructUtils
open DataStructShared
open P4IR
open TransUtils
open Collections

module CMS :
  DS with type opt_rec = sketch_opt_rec and type alloc_rec = sketch_alloc_rec =
struct
  type opt_rec = sketch_opt_rec

  type alloc_rec = sketch_alloc_rec

  let num_bit_per_slot = 32

  let dsname = "CountMinSketch"

  let get_alloc (reg_pairs : (int * int) list) : allocinfo list =
    List.filter_map
      (fun (w, r) ->
        if w * r > 16 then None
        else Some (AllocCMS {w; r; block= 0; num_slot_log2= 0}) )
      reg_pairs

  let add_block (bs_list : (int * int) list) (_ : opt_rec) (alloc : alloc_rec) :
      allocinfo list =
    let add_block' (block, num_slot_log2) =
      AllocCMS {alloc with block; num_slot_log2}
    in
    List.map add_block' bs_list

  let get_block_slot_pairs (opt : opt_rec) : int -> int -> (int * int) list =
    get_block_slot_pairs true num_bit_per_slot opt.num_dist_keys

  (* (\delta * 1 + (1-\delta) * \epsilon) *)
  let get_utility (w_pure_int : int) (time_hi : Z.t) (id : int) (syn : syninfo)
      (opt : opt_rec) (alloc : alloc_rec) (input_spec_map : input_map) : float =
    let r = float_of_int alloc.r in
    let num_slot = float_of_int (int_pow2 alloc.num_slot_log2) in
    let delta = F.exp (F.neg r) in
    let epsilon = F.div (F.exp 1.) num_slot in
    let du = F.add delta (F.mul (F.sub 1. delta) epsilon) in
    (* F.mul opt.qweight du *)
    du

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
    get_res_nodes true

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
            ( gen_p4expname ["value"]
            , gen_p4expr
                (ExpBinaryOp
                   ( PlusSat
                   , gen_p4expname ["value"]
                   , gen_p4expint 1 num_bit_per_slot ) ) )
        ; StatAssignment (gen_p4expname ["rv"], gen_p4expname ["value"]) ]
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
    let name = "tbl_cms" in
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

  let get_win_decl (p : string) (alloc : alloc_rec) : prog_tuple =
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
      let rec gen_act_body_list (tot : int) : P4.coq_StatementPreT list list =
        let gen_act_stmt (lo : int) (hi : int) : P4.coq_StatementPreT =
          let lo = string_of_int lo in
          let hi = string_of_int hi in
          StatAssignment
            ( gen_p4expname ["win_md"; "rw_" ^ lo]
            , gen_p4expr
                (ExpBinaryOp
                   ( PlusSat
                   , gen_p4expname ["win_md"; "rw_" ^ lo]
                   , gen_p4expname ["win_md"; "rw_" ^ hi] ) ) )
        in
        if tot = 1 then []
        else
          let curr_act_body =
            map_for_range
              (fun lo -> gen_act_stmt lo (((tot + 1) / 2) + lo))
              1 (tot / 2)
          in
          curr_act_body :: gen_act_body_list (int_cdiv tot 2)
      in
      let act_body_list = gen_act_body_list alloc.r in
      let num_acts = List.length act_body_list in
      let act_names =
        map_for_range (fun i -> "act_merge_rows_" ^ string_of_int i) 1 num_acts
      in
      let tbl_names =
        map_for_range (fun i -> "tbl_merge_rows_" ^ string_of_int i) 1 num_acts
      in
      ( List.map2 gen_p4act act_names act_body_list
      , List.map2 gen_p4tbl tbl_names act_names
      , List.map gen_p4tbl_call tbl_names )
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

  let gen_reg_decl (p : string) (syn : syninfo) (alloc : alloc_rec) : code_type
      =
    CodeP4 (union_prog_tuple (get_row_decl p syn alloc) (get_win_decl p alloc))

  let get_cap_decl (p : string) (syn : syninfo) (alloc : alloc_rec) :
      code_type option =
    let rec gen_act_body_list (tot : int) : P4.coq_StatementPreT list list =
      let gen_act_stmt (lo : int) (hi : int) : P4.coq_StatementPreT =
        let lo = string_of_int lo in
        let hi = string_of_int hi in
        StatAssignment
          ( gen_p4dsmd ["win_" ^ lo; "rw_1"]
          , gen_p4expr
              (ExpBinaryOp
                 ( PlusSat
                 , gen_p4dsmd ["win_" ^ lo; "rw_1"]
                 , gen_p4dsmd ["win_" ^ hi; "rw_1"] ) ) )
      in
      (* alloc.w >= 2 *)
      if tot = 2 then []
      else
        let curr_act_body =
          map_for_range
            (fun lo -> gen_act_stmt lo (((tot + 1) / 2) + lo))
            1 (tot / 2)
        in
        curr_act_body :: gen_act_body_list (int_cdiv tot 2)
    in
    let act_body_list = gen_act_body_list alloc.w in
    let num_acts = List.length act_body_list in
    let act_names =
      map_for_range (fun i -> "act_merge_wins_" ^ string_of_int i) 1 num_acts
    in
    let tbl_names =
      map_for_range (fun i -> "tbl_merge_wins_" ^ string_of_int i) 1 num_acts
    in
    let merge_actions = List.map2 gen_p4act act_names act_body_list in
    let merge_tbls = List.map2 gen_p4tbl tbl_names act_names in
    let merge_tbl_call = List.map gen_p4tbl_call tbl_names in
    let last_action : P4.coq_Declaration list =
      [ gen_p4act "act_merge_wins_final"
          [ StatAssignment
              ( gen_p4expname ["query_res"]
              , gen_p4expr
                  (ExpBinaryOp
                     ( PlusSat
                     , gen_p4dsmd ["win_1"; "rw_1"]
                     , gen_p4dsmd ["win_2"; "rw_1"] ) ) ) ] ]
    in
    let last_ks = [gen_catexpname ["api"]] in
    let last_mks = ["ternary"] in
    let get_centries (s : string) : cat_entry list =
      [MkCatEntry ([MIdent (gen_catname [s])], "act_merge_wins_final", [])]
    in
    let centries_query = get_centries "QUERY" in
    let centries_insquery = get_centries "INSQUERY" in
    let last_centries =
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
      win_entries @ [cat_act_dft (List.length last_ks)]
    in
    let last_name = "tbl_merge_wins_final" in
    let last_ctable =
      MkCatTable (last_name, last_ks, last_mks, last_centries)
    in
    let last_table = trans_table last_ctable in
    match syn.api_set with
    | ASI ->
        None
    | _ ->
        Some
          (CodeP4
             ( []
             , []
             , []
             , merge_actions @ merge_tbls @ last_action @ [last_table]
             , merge_tbl_call @ [gen_p4tbl_call last_name] ) )

  let get_res_nodes_and_p4 (p : string) (stage_hash : int) (stage_action : int)
      (max_hash_per_table : int) (min_bit_per_hash : int) (num_bit_in_ts : int)
      (max_idx_per_phv : int) (num_unit : Z.t) (unit_len_log2 : int)
      (var : Cid.t) (atomize : bool) (syn : syninfo) (opt : opt_rec)
      (alloc : alloc_rec) : (res_node list * code_type) list =
    let reg_decl = gen_reg_decl p syn alloc in
    let cap_decl = get_cap_decl p syn alloc in
    get_res_nodes_and_p4 dsname num_bit_per_slot reg_decl cap_decl p stage_hash
      stage_action max_hash_per_table min_bit_per_hash num_bit_in_ts
      max_idx_per_phv num_unit unit_len_log2 var atomize syn opt alloc
end
