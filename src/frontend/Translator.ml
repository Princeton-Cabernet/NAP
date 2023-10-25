open MiscUtils
open DagIR
open DataStructIR
open DataStructUtils
open DataStruct
open Allocator
open Pipeline
open P4IR
open TransUtils
open Template
open Format
open Collections

let api_vals =
  [ ("NOOP", "0")
  ; ("CLEAR", "1")
  ; ("INSERT", "2")
  ; ("QUERY", "3")
  ; ("INSQUERY", "4")
  ; ("UPDATE", "5")
  ; ("UPDQUERY", "6")
  ; ("DONTCARE", "0")
  ; ("QDEFAULT", "0") ]

let print_defines p (defines : (string * string) list) =
  fprintf p "@[<v 0>" ;
  let _ = List.map (fun (x, y) -> fprintf p "#define %s %s@," x y) defines in
  fprintf p "@]@,"

let add_init_to_meta (g : StG.t) : P4.coq_DeclarationField list =
  let get_decl_field (s : Cat.dag_stmt) =
    match s with
    | DSLocal (cid, ty, e) ->
        [ P4Alias.MkDeclarationField
            (noinfo, trans_type ty, to_p4str (Id.name (Cid.last_id cid))) ]
    | _ ->
        []
  in
  let add_init_to_meta' (n : StNode.t) (agg : P4.coq_DeclarationField list) =
    match n.s with
    | DSMatch ([], [([], merged_action)]) ->
        List.flatten (List.map get_decl_field merged_action) @ agg
    | _ ->
        agg
  in
  StG.fold_vertex add_init_to_meta' g []

type fit_result_type = Done of (int * bool) | NextStage of res_node

let is_done (fit_result : fit_result_type) =
  match fit_result with Done _ -> true | NextStage _ -> false

let fit_with_split_and_gen_p4 (pipe : pipe_type) (res : res_node)
    (table : (cat_table * cat_action list) option) (stage : int) (split : bool)
    : int * bool * prog_tuple =
  (* Printf.printf "%d %s\n" stage (string_of_resnode res) ; *)
  let rec fit_with_split' (pipe : pipe_type) (res : res_node)
      (table : (cat_table * cat_action list) option) (part_id : int)
      (stage : int) (split : bool) =
    let fit_result, num_placed_actions =
      if stage >= Array.length pipe then (Done (stage, false), 0)
      else if split then (
        assert (res.num_hash = 0) ;
        assert (res.num_reg = 0) ;
        assert (res.num_block = 0) ;
        assert (res.num_tbl = 1) ;
        if pipe.(stage).stage_table = 0 || pipe.(stage).stage_action = 0 then
          (NextStage res, 0)
        else if res.num_act <= pipe.(stage).stage_action then (
          pipe.(stage).stage_table <- pipe.(stage).stage_table - 1 ;
          pipe.(stage).stage_action <- pipe.(stage).stage_action - res.num_act ;
          (Done (stage, true), res.num_act) )
        else
          let num_act_placed = pipe.(stage).stage_action in
          pipe.(stage).stage_action <- 0 ;
          pipe.(stage).stage_table <- pipe.(stage).stage_table - 1 ;
          ( NextStage {res with num_act= res.num_act - num_act_placed}
          , num_act_placed ) )
      else
        let num_blocks = if res.num_block = 0 then 0 else res.num_block + 1 in
        (* res.m_hash = 1 *)
        if
          res.num_reg <= pipe.(stage).stage_reg
          && res.num_tbl <= pipe.(stage).stage_table
          && res.num_act <= pipe.(stage).stage_action
          && res.num_hash <= pipe.(stage).stage_hash
          && num_blocks <= pipe.(stage).stage_block
        then (
          pipe.(stage).stage_reg <- pipe.(stage).stage_reg - res.num_reg ;
          pipe.(stage).stage_table <- pipe.(stage).stage_table - res.num_tbl ;
          pipe.(stage).stage_action <- pipe.(stage).stage_action - res.num_act ;
          pipe.(stage).stage_hash <- pipe.(stage).stage_hash - res.num_hash ;
          pipe.(stage).stage_block <- pipe.(stage).stage_block - num_blocks ;
          (Done (stage, true), res.num_act) )
        else (NextStage res, 0)
    in
    let ptup, next_table, next_part_id =
      match table with
      | Some
          ( (MkCatTable (table_name, ks, mks, c_entries) as ctable)
          , unplaced_actions ) ->
          if num_placed_actions > 0 then (
            let placed_actions, unplaced_actions' =
              split_after_nth unplaced_actions (num_placed_actions - 1)
            in
            assert (List.length placed_actions = num_placed_actions) ;
            ( trans_stmt_match
                (MkCatTable
                   ( ( table_name
                     ^
                     if part_id = 1 && is_done fit_result then ""
                     else "_part_" ^ string_of_int part_id )
                   , ks
                   , mks
                   , c_entries ) )
                placed_actions
            , Some (ctable, unplaced_actions')
            , part_id + 1 ) )
          else (empty_prog_tuple, table, part_id)
      | None ->
          (empty_prog_tuple, None, part_id)
    in
    match fit_result with
    | NextStage res ->
        let stage, next_result, next_ptup =
          fit_with_split' pipe res next_table next_part_id (stage + 1) split
        in
        (stage, next_result, union_prog_tuple ptup next_ptup)
    | Done (stage, result) ->
        (stage, result, ptup)
  in
  fit_with_split' pipe res table 1 stage split

(* Assumptions:
   1. number of entries the same as the number of keys.
*)
let match_to_table (s : Cat.dag_stmt) (tbl_id : string) : code_type =
  match s with
  | DSMatch (ks, entries) ->
      let entry_to_action (act_map : action_name_map) (action_id : int)
          ((pats, action) : Cat.dag_branch) :
          int * bool list * cat_entry * cat_action list =
        let is_range =
          List.map
            (fun m -> match m with Cat.PRange _ -> true | _ -> false)
            pats
        in
        let matches = List.map (fun m -> MMatch m) pats in
        if List.length action > 0 then (
          match StmtsMap.find_option act_map action with
          | Some action_name ->
              (action_id, is_range, MkCatEntry (matches, action_name, []), [])
          | None ->
              let action_name =
                "act_for_tbl_" ^ tbl_id ^ "_action_" ^ string_of_int action_id
              in
              StmtsMap.replace act_map action action_name ;
              ( action_id + 1
              , is_range
              , MkCatEntry (matches, action_name, [])
              , [MkCatAction (action_name, [], action)] )
              (* NoAction not in the list of action declarations *) )
        else (action_id, is_range, MkCatEntry (matches, "NoAction", []), [])
      in
      let act_map = StmtsMap.create (List.length entries) in
      let rev_entries = List.rev entries in
      let _, is_range, c_entries, c_actions =
        List.fold_right
          (fun entry (id, accum1, accum2, accum3) ->
            let nid, is_range, centry, caction =
              entry_to_action act_map id entry
            in
            ( nid
            , List.map2 ( || ) is_range accum1
            , centry :: accum2
            , caction :: accum3 ) )
          rev_entries
          (0, list_repeat (List.length ks) false, [], [])
      in
      let mks = List.map (fun b -> if b then "range" else "ternary") is_range in
      let c_entries = List.rev c_entries in
      let c_actions = List.flatten (List.rev c_actions) in
      let table_name = "tbl_for_stmt_" ^ tbl_id in
      CodeTable (MkCatTable (table_name, ks, mks, c_entries), c_actions)
  | _ ->
      raise
        (Error "[Translator] Only expect to translate SMatch statement here.")

let union_two_ptups (code : prog_tuple)
    ((result, next_code, next_dscode) : bool * prog_tuple * prog_tuple option) =
  match next_dscode with
  | None ->
      (result, union_prog_tuple code next_code, None)
  | Some next_dscode' ->
      (result, next_code, Some (union_prog_tuple code next_dscode'))

let rec fit_multi_stage_and_gen_p4 (pipe : pipe_type)
    (res_code_list : (res_node list * code_type) list)
    (min_stage : (int * int) array) ((read_stage, write_stage) : int * int)
    (id : int) (fst_tbl : bool) (last_stages : int list option) :
    bool * prog_tuple * prog_tuple option =
  match res_code_list with
  | [] ->
      min_stage.(id) <- (fst min_stage.(id), read_stage) ;
      (true, empty_prog_tuple, None)
  | ([], CodeP4 code) :: tl ->
      let res_triplet =
        fit_multi_stage_and_gen_p4 pipe tl min_stage (read_stage, write_stage)
          id fst_tbl last_stages
      in
      union_two_ptups code res_triplet
  | ([], CodeCtrlEnd code) :: tl -> (
      let result, next_code, next_dscode =
        fit_multi_stage_and_gen_p4 pipe tl min_stage (read_stage, write_stage)
          id fst_tbl last_stages
      in
      match next_dscode with
      | None ->
          (result, union_prog_tuple code next_code, Some empty_prog_tuple)
      | Some next_dscode' ->
          raise
            (Error
               "[Translator] CodeCtrlBegin and CodeCtrlEnd must be paired and \
                sequential." ) )
  | ([], CodeCtrlBegin (name, params)) :: tl -> (
      let result, next_code, next_dscode =
        fit_multi_stage_and_gen_p4 pipe tl min_stage (read_stage, write_stage)
          id fst_tbl last_stages
      in
      match next_dscode with
      | None ->
          raise
            (Error
               "[Translator] CodeCtrlBegin and CodeCtrlEnd must be paired and \
                sequential." )
      | Some (top_decls, md_fields, ds_decls, ctrl_decls, ctrl_stmts) ->
          let ctrl = gen_p4ctrl name params ctrl_decls ctrl_stmts in
          let code = (top_decls, md_fields, ds_decls @ [ctrl], [], []) in
          (result, union_prog_tuple code next_code, None) )
  | (res_nodes, code) :: tl -> (
    match (res_nodes, code) with
    | [({typ= Table b; _} as res)], CodeTable (ctable, unplaced_actions) ->
        let stage' =
          if List.length tl = 0 then max read_stage write_stage else read_stage
        in
        let end_stage, result, ptup =
          fit_with_split_and_gen_p4 pipe res
            (Some (ctable, unplaced_actions))
            stage' true
        in
        if result then (
          (* Untested yet *)
          if fst_tbl then
            min_stage.(id) <- (end_stage, end_stage + if b then 1 else 0) ;
          let res_triplet =
            fit_multi_stage_and_gen_p4 pipe tl min_stage
              ((end_stage + if b then 1 else 0), write_stage)
              id false last_stages
          in
          union_two_ptups ptup res_triplet )
        else (result, ptup, None)
    | [({typ= Atom b; _} as res)], CodeTable (ctable, unplaced_actions) ->
        let stage' =
          if List.length tl = 0 then max read_stage write_stage else read_stage
        in
        let end_stage, result, ptup =
          fit_with_split_and_gen_p4 pipe res
            (Some (ctable, unplaced_actions))
            stage' false
        in
        if result then (
          if fst_tbl then
            min_stage.(id) <- (end_stage, end_stage + if b then 1 else 0) ;
          let res_triplet =
            fit_multi_stage_and_gen_p4 pipe tl min_stage
              ((end_stage + if b then 1 else 0), write_stage)
              id false last_stages
          in
          union_two_ptups ptup res_triplet )
        else (result, empty_prog_tuple, None)
    | l, CodeTable _ ->
        raise (Error "[Translator] Unexpected resource nodes and code pair.")
    | ({typ= Atom b; _} as res) :: res_tl, _ ->
        let stage' =
          if List.length tl = 0 then max read_stage write_stage else read_stage
        in
        let end_stage, result, _ =
          fit_with_split_and_gen_p4 pipe res None stage' false
        in
        if result then
          fit_multi_stage_and_gen_p4 pipe ((res_tl, code) :: tl) min_stage
            ((end_stage + if b then 1 else 0), write_stage)
            id fst_tbl last_stages
        else (result, empty_prog_tuple, None)
    | ({typ= Hash b; _} as res) :: res_tl, _ ->
        let stage' = snd min_stage.(id) in
        let end_stage, result, _ =
          fit_with_split_and_gen_p4 pipe res None stage' false
        in
        if result then
          ( min_stage.(id) <- (fst min_stage.(id), end_stage) ;
            fit_multi_stage_and_gen_p4 pipe ((res_tl, code) :: tl) min_stage
              (max (end_stage + if b then 1 else 0) read_stage, write_stage)
              id fst_tbl )
            last_stages
        else (result, empty_prog_tuple, None)
    | ({typ= Clear (b1, b2); _} as res) :: res_tl, _ ->
        let stage' = if b1 then fst min_stage.(id) else read_stage in
        let end_stage, result, _ =
          fit_with_split_and_gen_p4 pipe res None stage' false
        in
        if result then
          let next_stage =
            if b2 then max (snd min_stage.(id)) end_stage + 1 else end_stage + 1
          in
          fit_multi_stage_and_gen_p4 pipe ((res_tl, code) :: tl) min_stage
            (next_stage, write_stage) id fst_tbl last_stages
        else (result, empty_prog_tuple, None)
    | ({typ= Reg b1; num_reg= r; num_tbl= merge_r; _} as res) :: res_tl, _ ->
        let last_reg_stages =
          match last_stages with
          | None ->
              list_repeat r read_stage
          | Some l ->
              l
        in
        assert (List.length last_reg_stages == r) ;
        let each_res = {res with num_reg= 1; num_tbl= 1} in
        let merge_res =
          { typ= Atom true
          ; num_tbl= 1
          ; num_act= 1
          ; num_hash= 0
          ; num_reg= 0
          ; num_block= 0 }
        in
        let rec fit_one_reg (stage : int) (num_reg_unfit : int)
            (next_reg_stages : int list) =
          let stage' =
            max stage (List.nth last_reg_stages (r - num_reg_unfit))
          in
          let end_stage, result, _ =
            fit_with_split_and_gen_p4 pipe each_res None stage' false
          in
          let next_reg_stages' =
            (end_stage + if b1 then 1 else 0) :: next_reg_stages
          in
          if (not result) || num_reg_unfit = 1 then
            (end_stage, result, next_reg_stages')
          else fit_one_reg end_stage (num_reg_unfit - 1) next_reg_stages'
        in
        let rec fit_one_merge (stage : int) (num_values_to_merge : int) =
          let end_stage, result, _ =
            fit_with_split_and_gen_p4 pipe merge_res None stage true
          in
          if (not result) || num_values_to_merge = 2 then (end_stage, result)
          else fit_one_merge (end_stage + 1) (int_log2up num_values_to_merge)
        in
        let end_stage_reg, result_reg, next_reg_stages = fit_one_reg 0 r [] in
        if not result_reg then (result_reg, empty_prog_tuple, None)
        else if merge_r >= 2 then
          let end_stage_merge, result_merge =
            fit_one_merge (end_stage_reg + 1) merge_r
          in
          if not result_merge then (result_merge, empty_prog_tuple, None)
          else
            (* print_string "Done\n" ; *)
            fit_multi_stage_and_gen_p4 pipe ((res_tl, code) :: tl) min_stage
              ((if b1 then end_stage_merge + 1 else end_stage_reg), write_stage)
              id fst_tbl (Some next_reg_stages)
        else
          fit_multi_stage_and_gen_p4 pipe ((res_tl, code) :: tl) min_stage
            ((if b1 then end_stage_reg + 1 else end_stage_reg), write_stage)
            id fst_tbl (Some next_reg_stages)
    | _ ->
        raise (Error "[Translator] Unexpected resource nodes and code pair.") )

let get_table_from_stmt (s : dag_stmt) : dag_stmt =
  match s with
  | DSAssign _ ->
      DSMatch ([], [([], [s])])
  | DSMatch _ ->
      s
  | _ ->
      raise (Error "[Translator] No other statements are converted into SMatch.")

(* optinfo list list * allocinfo list * bool
   : prog_triple * allocinfo list*)
let trans_node (tu_map : time_map) (table_map : res_map) (pipe : pipe_type)
    (min_stage : (int * int) array) (atomize : bool) (n : StNode.t)
    ((prev_ptup, syn_list, opt_choices, alloc_list, result) :
      prog_tuple * syninfo list * optinfo list list * allocinfo list * bool ) =
  match n.s with
  | DSNoop ->
      (prev_ptup, syn_list, opt_choices, alloc_list, result)
  | DSDataStruct set_info -> (
    match (syn_list, opt_choices, alloc_list) with
    | syn :: syn_tl, opt :: opt_tl, alloc :: alloc_tl ->
        let res_code_list =
          get_res_nodes_and_p4 Tofino.stage_hash Tofino.stage_action
            Tofino.max_hash_per_table Tofino.min_bit_per_hash
            Tofino.num_bit_in_ts Tofino.max_idx_per_phv tu_map n.id
            set_info.res_var atomize syn opt alloc
        in
        let result, ptup, _ =
          fit_multi_stage_and_gen_p4 pipe res_code_list min_stage
            min_stage.(n.id) n.id true None
        in
        (union_prog_tuple prev_ptup ptup, syn_tl, opt_tl, alloc_tl, result)
    | _ ->
        raise
          (Error
             "[Translator] Fewer alloc objects than expected during allocation."
          ) )
  | DSAssign _ | DSMatch _ ->
      let table = get_table_from_stmt n.s in
      let tbl_id = if n.id = -1 then "md_setup" else string_of_int n.id in
      let codetable = match_to_table table tbl_id in
      let res = IntMap.find table_map n.id in
      let rw_stage = max (fst min_stage.(n.id)) (snd min_stage.(n.id)) in
      let result, ptup, _ =
        fit_multi_stage_and_gen_p4 pipe
          [([res], codetable)]
          min_stage (rw_stage, rw_stage) n.id true None
      in
      ( union_prog_tuple prev_ptup ptup
      , syn_list
      , opt_choices
      , alloc_list
      , result )
  | DSLocal _ ->
      raise (Error "[Translator] DSLocal statements should have been resolved.")
  | DSUnit _ ->
      raise (Error "[Translator] DSUnit statements should have been saved.")

let exit_early_for_print
    ((_, _, _, _, result) :
      prog_tuple * syninfo list * optinfo list list * allocinfo list * bool ) =
  result = false

let common_decls : P4.coq_Declaration list * P4.coq_Declaration list =
  ( [ gen_p4decltypedef "api_t" num_bit_api_call
    ; gen_p4decltypedef "window_t" num_bit_window_t
    ; gen_p4decltypedef "pred_t" num_bit_pred ]
  , [ DeclStruct
        ( noinfo
        , to_p4str "window_pair_t"
        , [ MkDeclarationField
              (noinfo, TypTypeName (to_p4str "window_t"), to_p4str "lo")
          ; MkDeclarationField
              (noinfo, TypTypeName (to_p4str "window_t"), to_p4str "hi") ] ) ]
  )

let assemble_prog
    ((top_decls, md_fields, ds_decls, ig_decls, ig_stmts) : prog_tuple) :
    P4.coq_Declaration list =
  let md_decl : P4.coq_Declaration =
    DeclStruct (noinfo, to_p4str "metadata_t", md_fields)
  in
  let ig_ctrl =
    gen_p4ctrl "SwitchIngress"
      [ (InOut, TypTypeName (to_p4str "header_t"), "hdr")
      ; (InOut, TypTypeName (to_p4str "metadata_t"), "ig_md")
      ; (In, TypTypeName (to_p4str "ingress_intrinsic_metadata_t"), "ig_intr_md")
      ; ( In
        , TypTypeName (to_p4str "ingress_intrinsic_metadata_from_parser_t")
        , "ig_intr_prsr_md" )
      ; ( InOut
        , TypTypeName (to_p4str "ingress_intrinsic_metadata_for_deparser_t")
        , "ig_intr_dprsr_md" )
      ; ( InOut
        , TypTypeName (to_p4str "ingress_intrinsic_metadata_for_tm_t")
        , "ig_intr_tm_md" ) ]
      ig_decls ig_stmts
  in
  fst common_decls @ top_decls @ [md_decl] @ snd common_decls @ parser_decls
  @ ds_decls @ [ig_ctrl] @ deparser_decls

(*: P4.coq_Declaration list*)
let trans_prog (p : formatter) (max_id : int) (root : StNode.t) (dag : StG.t)
    (syn_list : syninfo list) (opt_choices : optinfo list list)
    (alloc_list : allocinfo list) (tu_map : time_map) (atomize : bool) =
  let t0 = Sys.time () in
  let table_map = IntMap.create (StG.nb_vertex dag) in
  StT.simple_iter (res_of_table table_map atomize) dag root ;
  let pipe = Array.init Tofino.num_stage (fun _ -> Tofino.gen_stage ()) in
  let min_stage = Array.make (max_id + 1) (-1, -1) in
  let local_metafields = add_init_to_meta dag in
  let program =
    match
      StT.fold
        (trans_node tu_map table_map pipe min_stage atomize)
        (decide_earliest_stage min_stage)
        exit_early_for_print dag root
        (empty_prog_tuple, syn_list, opt_choices, alloc_list, true)
    with
    | ptup, [], [], [], true ->
        assemble_prog (union_prog_tuple ptup ([], local_metafields, [], [], []))
    | _, _, _, _, _ ->
        raise (Error "[Translator] Translation failed for the best allocation.")
  in
  print_defines p api_vals ;
  Petr4.Printp4.print_program p
    ["<core.p4>"; "<tna.p4>"; "\"common/headers.p4\""; "\"common/util.p4\""]
    [] (*"@pragma pa_auto_init_metadata"*) program ;
  let t1 = Sys.time () in
  Printf.printf "[Translator] Time to translate to P4: %.8fs\n" (t1 -. t0)
