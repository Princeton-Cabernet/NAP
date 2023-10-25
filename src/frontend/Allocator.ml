open Syntax
open SyntaxUtils
open MiscUtils
open SetIR
open DagIR
open Collections
open Pipeline
open DataStruct
open DataStructIR
open DataStructUtils
open TransUtils
module StT = Traverser.Make (StG)

type res_map = res_node IntMap.t

type stmts_set = unit StmtsMap.t

type pipe_type = Tofino.stage_type array

(* Assumptions:
    1. SLocal not necesssarily equal to 0
    2. SLocal all moved to the front of the program
    3. SLocal for all local variables *)
let merge_svar (root : StNode.t) (dag : StG.t) : StG.t =
  let first_stage_nodes = StG.succ dag root in
  let is_init_node n = match n.StNode.s with DSLocal _ -> true | _ -> false in
  let init_nodes = List.filter is_init_node first_stage_nodes in
  if List.length init_nodes > 0 then (
    let merged_action =
      List.fold_left (fun agg n -> n.StNode.s :: agg) [] init_nodes
    in
    let merged_id =
      List.fold_left
        (fun id n -> if n.StNode.id > id then n.StNode.id else id)
        (-1) init_nodes
    in
    let init_table = DSMatch ([], [([], merged_action)]) in
    let init_node = {StNode.id= merged_id; s= init_table} in
    let succ_nodes_labels =
      List.map
        (fun edge -> (StG.E.dst edge, StG.E.label edge))
        (List.map (StG.succ_e dag) init_nodes |> List.flatten)
    in
    List.iter (fun n -> StG.remove_vertex dag n) init_nodes ;
    StG.add_vertex dag init_node ;
    StG.add_edge_e dag (root, 1, init_node) ;
    List.iter
      (fun (succ, weight) -> StG.add_edge_e dag (init_node, weight, succ))
      succ_nodes_labels ;
    dag )
  else dag

let decide_ds (n : StNode.t) : (int * syninfo * optinfo list) option =
  match n.StNode.s with
  | DSDataStruct set_info -> (
      let num_dist_keys =
        List.length
          (list_uniq (List.map (fun (_, _, keys) -> keys) set_info.branches))
      in
      let all_apis = List.map (fun (_, api, _) -> api) set_info.branches in
      let api_set =
        match
          ( List.mem AInsert all_apis
          , List.mem AQuery all_apis
          , List.mem AInsQuery all_apis )
        with
        | false, false, false ->
            raise
              (Error
                 "[Allocator] Trivial match statements should have been \
                  removed in Dataflow." )
        | false, false, true ->
            ASInQ
        | false, true, false ->
            ASQ
        | false, true, true ->
            ASQInQ
        | true, false, false ->
            ASI
        | true, false, true ->
            ASIInQ
        | true, true, false ->
            ASIQ
        | true, true, true ->
            ASIQInQ
      in
      let has_clear_branch = List.mem AClear all_apis in
      let syn : syninfo =
        { set_name= set_info.set_name
        ; keys_ty= set_info.keys_ty
        ; time_fun= set_info.time_fun
        ; query_fun= set_info.query_fun
        ; match_keys= set_info.match_keys
        ; branches= set_info.branches
        ; has_clear_branch
        ; api_set }
      in
      let num_apis = get_num_apis api_set in
      let num_reg_progs_sketch = get_num_reg_progs api_set false in
      let num_reg_progs_fold = get_num_reg_progs api_set true in
      match (set_info.query_fun, set_info.err) with
      | QExist, Approxset | QExist, Superset ->
          Some
            ( n.StNode.id
            , syn
            , [ OptBloom
                  {num_dist_keys; num_apis; num_reg_progs= num_reg_progs_sketch}
              ] )
      | QCount, Approxset | QCount, Superset ->
          Some
            ( n.StNode.id
            , syn
            , [ OptCMS
                  {num_dist_keys; num_apis; num_reg_progs= num_reg_progs_sketch}
              ] )
      | QFold (init, upd, index), _ ->
          let len_init = List.length init in
          let len_upd = List.length upd in
          if
            len_init <= max_reg_entries
            && len_init >= 1 && len_init = len_upd && index < len_init
            && index >= 0
          then
            Some
              ( n.StNode.id
              , syn
              , [ OptFold
                    { num_dist_keys
                    ; num_apis
                    ; num_reg_progs= num_reg_progs_fold
                    ; err= set_info.err
                    ; num_entries= List.length init
                    ; key_length=
                        (let key_length = numeric_raw_ty_size syn.keys_ty in
                         key_length ) } ] )
          else
            raise
              (Error
                 "[Allocator] Unexpected number of init/update entries or \
                  unexpected index." )
      (* | AggExist ErrNeg
         | AggCount ErrDontCare (Some n)
         | AggCount ErrPos (Some n)
         | AggCount ErrPos None
         | AggCount ErrNeg None
             percent & actions
         | AggCountDist ErrDontCare
         | AggFold init upd index (*extra checks like num_api_calls = 1 and num_dist_keys = 1*)*)
      | _ ->
          raise (Error "Not implemented yet.") )
  | _ ->
      None

(* Dummy *)
let get_input_spec (syn_list : syninfo list) (opt_lists : optinfo list list) :
    input_map =
  InputSpec.input_spec_map

let calc_utility (dag : StG.t) (root : StNode.t) :
    int list
    * syninfo list
    * optinfo list list
    * (float * allocinfo list) list
    * time_map =
  let store_ds (v : StNode.t) (agg : int list * syninfo list * optinfo list list)
      =
    Printf.printf "\tNode %d visited\n" v.id ;
    match decide_ds v with
    | None ->
        agg
    | Some (id, syn, opt) ->
        let aggids, aggsyns, agglists = agg in
        let aggids = id :: aggids in
        let agglists = opt :: agglists in
        let aggsyns = syn :: aggsyns in
        (aggids, aggsyns, agglists)
  in
  Printf.printf "[Allocator] Topological order of visiting nodes:\n" ;
  (* Use StT.fold so that info is saved in the same order as accessing in allocation *)
  let id_list, syn_list, opt_choices =
    StT.simple_fold store_ds dag root ([], [], [])
  in
  let id_list = List.rev id_list in
  let syn_list = List.rev syn_list in
  let opt_choices = List.rev opt_choices in
  let tot_reg = Tofino.num_stage * Tofino.stage_reg in
  let max_block = Tofino.num_stage * Tofino.stage_block in
  let tu_map, ds_set =
    get_time_utility Tofino.num_bit_in_ts tot_reg id_list syn_list
  in
  let opt_choices = filter_opt_choices ds_set id_list syn_list opt_choices in
  let opt_lists = cross_prod opt_choices in
  let num_queries = List.length (List.hd opt_lists) in
  if num_queries > tot_reg then
    raise (Error "[Allocator] The number of queries > the available registers.") ;
  let input_spec_map = get_input_spec syn_list opt_lists in
  (* The order of opt_list and alloc_list must be preserved! *)
  let for_every_ds_combo (opt_list : optinfo list) =
    let alloc_lists = get_alloc_lists tot_reg syn_list opt_list in
    let alloc_lists = quick_check_reg tot_reg alloc_lists in
    let alloc_lists = dup_paired_param_ds tu_map id_list syn_list alloc_lists in
    let alloc_lists =
      add_num_block Tofino.max_block_per_reg max_block Tofino.num_bit_per_block
        opt_list alloc_lists
    in
    (* let _ =
         List.map
           (fun alloc ->
             Printf.printf "%s\n" (string_of_allocinfo (List.hd alloc)) )
           alloc_lists
       in *)
    get_utility Tofino.num_bit_in_ts tu_map id_list syn_list opt_list
      alloc_lists input_spec_map
  in
  let u_alloc_list = list_map for_every_ds_combo opt_lists |> list_flatten in
  ( id_list
  , syn_list
  , opt_choices
  , List.sort
      (fun tup1 tup2 ->
        let comp_res = Stdlib.compare (fst tup1) (fst tup2) in
        if comp_res <> 0 then comp_res else Stdlib.compare (snd tup1) (snd tup2)
        )
      u_alloc_list
  , tu_map )

let res_of_table (agg : res_map) (atomize : bool) (n : StNode.t) : unit =
  match n.s with
  | DSNoop ->
      ()
  | DSDataStruct _ ->
      ()
  | DSAssign _ ->
      IntMap.replace agg n.id
        { typ= (if atomize then Atom false else Table false)
        ; num_tbl= 1
        ; num_act= 1
        ; num_hash= 0
        ; num_reg= 0
        ; num_block= 0 }
  | DSMatch (_, entries) ->
      let action_set = StmtsMap.create (List.length entries) in
      let add_action_list ((pats, ss) : dag_branch) =
        if List.length ss > 0 then StmtsMap.replace action_set ss ()
      in
      List.iter add_action_list entries ;
      let num_actions = StmtsMap.length action_set in
      IntMap.replace agg n.id
        { typ= (if atomize then Atom false else Table false)
        ; num_tbl= 1
        ; num_act= num_actions
        ; num_hash= 0
        ; num_reg= 0
        ; num_block= 0 }
  | DSLocal _ ->
      raise (Error "[Allocator] DSLocal statements should have been resolved.")
  | DSUnit _ ->
      raise (Error "[Allocator] DSUnit statements should have been saved.")

let decide_earliest_stage (min_stage : (int * int) array) (src_node : StNode.t)
    (dst_node : StNode.t) (dep : int) : unit =
  if dep = 0 then
    let prev_read_stage = fst min_stage.(src_node.id) in
    let old_read_stage = snd min_stage.(dst_node.id) in
    let new_read_stage = max prev_read_stage old_read_stage in
    min_stage.(dst_node.id) <- (fst min_stage.(dst_node.id), new_read_stage)
  else if dep = 1 then
    let prev_write_stage = snd min_stage.(src_node.id) + 1 in
    let old_write_stage = fst min_stage.(dst_node.id) in
    let new_write_stage = max prev_write_stage old_write_stage in
    min_stage.(dst_node.id) <- (new_write_stage, snd min_stage.(dst_node.id))
  else if dep = 2 then
    let prev_write_stage = snd min_stage.(src_node.id) + 1 in
    let old_write_stage = snd min_stage.(dst_node.id) in
    let new_write_stage = max prev_write_stage old_write_stage in
    min_stage.(dst_node.id) <- (fst min_stage.(dst_node.id), new_write_stage)

let rec fit_with_split (pipe : pipe_type) (res : res_node) (stage : int)
    (split : bool) (verbose : bool) : int * bool =
  if verbose then Printf.printf "%s\n" (string_of_resnode res) ;
  if stage >= Array.length pipe then (stage, false)
  else if split then (
    assert (res.num_reg = 0) ;
    assert (res.num_block = 0) ;
    assert (res.num_tbl = 1) ;
    if pipe.(stage).stage_table = 0 then (
      if verbose then
        Printf.printf "Failed at %d.\t%s\n" stage (string_of_stage pipe.(stage)) ;
      fit_with_split pipe res (stage + 1) split verbose )
    else if res.num_act <= pipe.(stage).stage_action then (
      pipe.(stage).stage_table <- pipe.(stage).stage_table - 1 ;
      pipe.(stage).stage_action <- pipe.(stage).stage_action - res.num_act ;
      if verbose then
        Printf.printf "Placed at %d.\t%s\n" stage (string_of_stage pipe.(stage)) ;
      (stage, true) )
    else if pipe.(stage).stage_action = 0 then (
      if verbose then
        Printf.printf "Failed at %d.\t%s\n" stage (string_of_stage pipe.(stage)) ;
      fit_with_split pipe res (stage + 1) split verbose )
    else
      let num_act_placed = pipe.(stage).stage_action in
      pipe.(stage).stage_action <- 0 ;
      pipe.(stage).stage_table <- pipe.(stage).stage_table - 1 ;
      if verbose then
        Printf.printf "Partial at %d.\t%s\n" stage
          (string_of_stage pipe.(stage)) ;
      fit_with_split pipe
        {res with num_act= res.num_act - num_act_placed}
        (stage + 1) split verbose )
  else
    let num_blocks = if res.num_block = 0 then 0 else res.num_block + 1 in
    (* Printf.printf "%d \n" num_blocks ; *)
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
      if verbose then
        Printf.printf "Placed at %d.\t%s\n" stage (string_of_stage pipe.(stage)) ;
      (stage, true) )
    else (
      if verbose then
        Printf.printf "Failed at %d.\t%s\n" stage (string_of_stage pipe.(stage)) ;
      fit_with_split pipe res (stage + 1) split verbose )

(* Assumptions:
   1. Two kinds of res_nodes: | [Table/Atom false]
                              | [Table/Atom false; Hash; Clear; API ...; Atom false]
       - The first table sets the read stage.
       - After the last table/atom, the write stage is set, which is equal to the
         end stage of the last item.
       - The last atom must be placed >= the write stage.
*)
let rec fit_multi_stage (pipe : pipe_type) (res_nodes : res_node list)
    (min_stage : (int * int) array) ((read_stage, write_stage) : int * int)
    (id : int) (fst_tbl : bool) (last_stages : int list option) (verbose : bool)
    : bool =
  match res_nodes with
  (* Last one *)
  | ({typ= Table b; _} as res) :: tl ->
      let stage' =
        if List.length tl = 0 then max read_stage write_stage else read_stage
      in
      let end_stage, result = fit_with_split pipe res stage' true verbose in
      if result then (
        if fst_tbl then
          min_stage.(id) <- (end_stage, end_stage + if b then 1 else 0) ;
        fit_multi_stage pipe tl min_stage
          ((end_stage + if b then 1 else 0), write_stage)
          id false last_stages verbose )
      else result
  | ({typ= Atom b; _} as res) :: tl ->
      let stage' =
        if List.length tl = 0 then max read_stage write_stage else read_stage
      in
      let end_stage, result = fit_with_split pipe res stage' false verbose in
      if result then (
        if fst_tbl then
          min_stage.(id) <- (end_stage, end_stage + if b then 1 else 0) ;
        fit_multi_stage pipe tl min_stage
          ((end_stage + if b then 1 else 0), write_stage)
          id false last_stages verbose )
      else result
  | ({typ= Hash b; _} as res) :: tl ->
      let stage' = snd min_stage.(id) in
      let end_stage, result = fit_with_split pipe res stage' false verbose in
      if result then (
        min_stage.(id) <- (fst min_stage.(id), end_stage) ;
        fit_multi_stage pipe tl min_stage
          (max (end_stage + if b then 1 else 0) read_stage, write_stage)
          id fst_tbl last_stages verbose )
      else result
  | ({typ= Clear (b1, b2); _} as res) :: tl ->
      let stage' = if b1 then fst min_stage.(id) else read_stage in
      let end_stage, result = fit_with_split pipe res stage' false verbose in
      if result then
        let next_stage =
          if b2 then max (snd min_stage.(id)) end_stage + 1 else end_stage + 1
        in
        fit_multi_stage pipe tl min_stage (next_stage, write_stage) id fst_tbl
          last_stages verbose
      else result
  | ({typ= Reg b1; num_reg= r; num_tbl= merge_r; _} as res) :: tl ->
      let last_reg_stages =
        match last_stages with None -> list_repeat r read_stage | Some l -> l
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
        let stage' = max stage (List.nth last_reg_stages (r - num_reg_unfit)) in
        let end_stage, result =
          fit_with_split pipe each_res stage' false verbose
        in
        let next_reg_stages' =
          (end_stage + if b1 then 1 else 0) :: next_reg_stages
        in
        if (not result) || num_reg_unfit = 1 then
          (end_stage, result, next_reg_stages')
        else fit_one_reg end_stage (num_reg_unfit - 1) next_reg_stages'
      in
      (* fit_with_split here; NOT fit_multi_stage *)
      let rec fit_one_merge (stage : int) (num_values_to_merge : int) =
        let end_stage, result =
          fit_with_split pipe merge_res stage true verbose
        in
        if (not result) || num_values_to_merge = 2 then (end_stage, result)
        else fit_one_merge (end_stage + 1) (int_log2up num_values_to_merge)
      in
      let end_stage_reg, result_reg, next_reg_stages = fit_one_reg 0 r [] in
      if not result_reg then result_reg
      else if merge_r >= 2 then
        let end_stage_merge, result_merge =
          fit_one_merge (end_stage_reg + 1) merge_r
        in
        if not result_merge then result_merge
        else
          (* print_string "Done\n" ; *)
          fit_multi_stage pipe tl min_stage
            ((if b1 then end_stage_merge + 1 else end_stage_reg), write_stage)
            id fst_tbl (Some next_reg_stages) verbose
      else
        fit_multi_stage pipe tl min_stage
          ((if b1 then end_stage_reg + 1 else end_stage_reg), write_stage)
          id fst_tbl (Some next_reg_stages) verbose
  | [] ->
      min_stage.(id) <- (fst min_stage.(id), read_stage) ;
      true

(* SEmpty, once guaranteed to be fully removed in dataflow.ml,
   can reappear in the root node. *)
let fit_one_alloc (tu_map : time_map) (table_map : res_map) (pipe : pipe_type)
    (min_stage : (int * int) array) (atomize : bool) (verbose : bool)
    (n : StNode.t)
    ((syn_list, opt_choices, alloc_list, result) :
      syninfo list * optinfo list list * allocinfo list * bool ) :
    syninfo list * optinfo list list * allocinfo list * bool =
  match n.s with
  | DSNoop ->
      (syn_list, opt_choices, alloc_list, result)
  | DSDataStruct _ -> (
    match (syn_list, opt_choices, alloc_list) with
    | syn :: syn_tl, opt_list :: opt_tl, alloc :: alloc_tl ->
        let res_nodes =
          get_res_nodes Tofino.stage_hash Tofino.stage_action
            Tofino.max_hash_per_table Tofino.min_bit_per_hash
            Tofino.num_bit_in_ts Tofino.max_idx_per_phv tu_map n.id atomize syn
            opt_list alloc
        in
        if verbose then Printf.printf "Try %s\n" (string_of_allocinfo alloc) ;
        ( syn_tl
        , opt_tl
        , alloc_tl
        , fit_multi_stage pipe res_nodes min_stage min_stage.(n.id) n.id true
            None verbose )
    | _, _, _ ->
        raise
          (Error
             "[Allocator] Fewer opt and alloc objects than expected during \
              allocation." ) )
  | DSAssign _ | DSMatch _ ->
      let res = IntMap.find table_map n.id in
      let rw_stage = max (fst min_stage.(n.id)) (snd min_stage.(n.id)) in
      let result =
        fit_multi_stage pipe [res] min_stage (rw_stage, rw_stage) n.id true None
          verbose
      in
      (syn_list, opt_choices, alloc_list, result)
  | DSLocal _ ->
      raise (Error "[Allocator] DSLocal statements should have been resolved.")
  | DSUnit _ ->
      raise (Error "[Allocator] DSUnit statements should have been saved.")

let exit_early
    ((_, _, _, result) :
      syninfo list * optinfo list list * allocinfo list * bool ) =
  result = false

let fit_df_dag (dag : StG.t) (max_id : int) (root : StNode.t)
    (syn_list : syninfo list) (opt_choices : optinfo list list)
    (au_list : (float * allocinfo list) list) (tu_map : time_map)
    (atomize : bool) (verbose : bool) =
  let table_map = IntMap.create (StG.nb_vertex dag) in
  StT.simple_iter (res_of_table table_map atomize) dag root ;
  let rec fit_df_dag' au_list rank =
    match au_list with
    | (u, alloc_list) :: tl -> (
        if verbose then Printf.printf "\n" ;
        let pipe = Array.init Tofino.num_stage (fun _ -> Tofino.gen_stage ()) in
        let min_stage = Array.make (max_id + 1) (-1, -1) in
        match
          StT.fold
            (fit_one_alloc tu_map table_map pipe min_stage atomize verbose)
            (decide_earliest_stage min_stage)
            exit_early dag root
            (syn_list, opt_choices, alloc_list, true)
        with
        | _, _, _, false ->
            fit_df_dag' tl (rank + 1)
        | [], [], [], true ->
            (rank, u, alloc_list)
        | _, _, _, true ->
            raise
              (Error
                 "More opt and alloc objects than expected during allocation."
              ) )
    | [] ->
        raise
          (Error
             "[Allocator] The program cannot fit into the current target. \
              Please consider reducing your program size, allowing query \
              errors, loosening time bounds, or increaseing target resource." )
  in
  fit_df_dag' au_list 1

let get_best_fit (max_id : int) (root : StNode.t) (df_dag : StG.t)
    (atomize : bool) (verbose : bool) :
    StG.t * syninfo list * optinfo list list * allocinfo list * time_map =
  let t0 = Sys.time () in
  let dag = merge_svar root df_dag in
  Printf.printf
    "[Allocator] Dataflow graph after merging variable declarations:\n" ;
  print_df_dag dag ;
  let t1 = Sys.time () in
  let id_list, syn_list, opt_choices, au_list, tu_map = calc_utility dag root in
  let t2 = Sys.time () in
  Printf.printf "[Allocator] List of synthesis information:\n" ;
  print_syninfo_list id_list syn_list ;
  Printf.printf "[Allocator] List of optimization information:\n" ;
  print_optinfo_choices id_list opt_choices ;
  Printf.printf "[Allocator] Number of configurations to consider:\n\t%d\n"
    (List.length au_list) ;
  print_tu_map tu_map ;
  Printf.printf "[Allocator] Utility and configurations:\n" ;
  print_au_list au_list (if verbose then None else Some 100) ;
  let t3 = Sys.time () in
  let rank, utility, alloc_list =
    fit_df_dag dag max_id root syn_list opt_choices au_list tu_map atomize
      verbose
  in
  let t4 = Sys.time () in
  Printf.printf "[Allocator] Optimal rank: %d\n" rank ;
  Printf.printf "[Allocator] Optimal utility: %f\n" utility ;
  Printf.printf "[Allocator] Optimal allocation: \n" ;
  print_string (string_of_alloc_list alloc_list) ;
  print_string "\n" ;
  Printf.printf "[Allocator] Time to optimize the DAG: %.8fs\n" (t1 -. t0) ;
  Printf.printf "[Allocator] Time to create %d configurations: %.8fs\n"
    (List.length au_list) (t2 -. t1) ;
  Printf.printf "[Allocator] Time to find the optimal configuration: %.8fs\n"
    (t4 -. t3) ;
  (dag, syn_list, opt_choices, alloc_list, tu_map)

(* 1. check float precision
   2. check results in jupyter notebook
   3. print to p4
   4. compile in p4 *)

(* StT.fold -> resource list of non-query nodes
   StT.fold -> use the previous results; generate resource of query nodes
   first fit =>
   StT.fold -> printP4 ( generic; query-based ) *)

(*
   change later SConditional into SMatch
   branch elimination -> merge
   merge 0-dependency and parallel nodes to reduce the number of actions/tables
   more early rejection by resource constraints
*)

(*
  1. merge
  2. data structure gives node structure
  3. generate tree of resources
  4. calculate the rank of utility
  5. try to fit with the tree of resources
*)
