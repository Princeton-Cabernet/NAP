open Syntax
open SyntaxUtils
open Printing
open Collections
open MiscUtils
open SetUtils
open Pipeline
open SetIR
open DagIR

let check_num_args_df = check_num_args "Dataflow"

(*
   The goal of preproc_cstr_types is to get rid of all constructor variables.
   When having very flexible constructor type usage like:
     dir_type dir = OUT;
     match p.ig_intr_md.ingress_port with
     | 0 -> { dir = OUT; }
     | _ -> { dir = IN; }
     match dir, x with
     | OUT, v1 -> ....
     | OUT, v2 -> ....

     We need to refine vi to make all patterns mutually exclusive,
     and then cross product the constructor variable's match patterns
     with other patterns.

     One difficult case:
     | OUT, 1 -> ...
     | IN, 1..2 -> ...
     | OUT, 1..3 -> ...
     It is hard to know what to do in the cross product of "OUT_pattern, 1..2"

     When x is also an constructor variable, things can be easier since
     contructors are mutually exclusive.
*)
let preproc_cstr_types (prog : decl list) = prog

(* Rearrange statements so that
    1. All match statements containing set module only contains set operations.
    2. Every set's operations are arranged into one single match statements by the name,
       i.e. ERecord and ECall are only in the match statement.
    3. Every match statement containing Set operations only has one restult variable.
    4. Every match statement has no dependence within itself.
    5. All match statements are unnested.
    6. All SNoop should be removed.
    7. Match branches should not contain SLocal i.e. variable declaration to avoid
       uninitialized values.
    8. SLocal should be used for new variables (i.e. no existing variable can be SLocal),
       and SLocal should use constants (i.e. SLocal with variables should add an SAssign),
       so that all SLocals can be moved to the front.
    9, Match statement with all empty branches removed.
    10. SUnit should be only for set operations and moved into match statement.
*)
let preproc_match_stmts (prog : decl list) = prog

(* 1. Replace ERecord and EWith with single variables
      (Exception: ERecord in ECall.)
   2. ERecord and ECall only appears in the match statement.
*)
let preproc_exp (prog : decl list) = prog

let preproc_set_node = ()

type userty_map_ty = raw_ty StrMap.t

(* key_type, error_direction * time window *)
type set_map_ty = (raw_ty * err * time_fun * query_fun) StrMap.t

type upd_map_ty = update list StrMap.t

let rec get_userty (cid : Cid.t) (userty_map : userty_map_ty) : raw_ty =
  let rec get_record_field cid ty =
    match (cid, ty) with
    | Id id, TRecord fields ->
        get_from_fields (Id.name id) fields
    | Compound (id, cid'), TRecord fields -> (
      match get_from_fields (Id.name id) fields with
      | Some ty ->
          get_record_field cid' ty
      | _ ->
          None )
    | _ ->
        None
  in
  match cid with
  | Id id -> (
    match StrMap.find_option userty_map (Id.name id) with
    | Some ty -> (
      match ty with
      | TName (cid', [], true) ->
          get_userty cid' userty_map
      | _ ->
          ty )
    | None ->
        raise (Error "[Dataflow] User-defined type not found.") )
  | Compound (id, cid') -> (
    match StrMap.find_option userty_map (Id.name id) with
    | Some ty -> (
      match ty with
      | TName (cid', [], true) ->
          get_userty cid' userty_map
      | _ -> (
        match get_record_field cid' ty with
        | Some ty ->
            ty
        | None ->
            raise (Error "[Dataflow] User-defined type not found.") ) )
    | None ->
        raise (Error "[Dataflow] User-defined type not found.") )

let cid_to_name (position : string) (cid : Cid.t) : string =
  let cid_names = Cid.names cid in
  if List.length cid_names <> 1 then
    raise
      (Error
         ( "[Dataflow] Unable to convert cid with multiple parts into id in "
         ^ position ^ "." ) )
  else List.hd cid_names

let exp_to_name (position : string) (exp : exp) : string =
  match exp.e with
  | EVar cid ->
      cid_to_name position cid
  | _ ->
      raise
        (Error
           ( "[Dataflow] Unable to convert expression to cid in " ^ position
           ^ "." ) )

let exp_to_cid (position : string) (exp : exp) : Cid.t =
  match exp.e with
  | EVar cid ->
      cid
  | _ ->
      raise
        (Error
           ( "[Dataflow] Unable to convert expression to cid in " ^ position
           ^ "." ) )

let get_err (arg : exp) : err =
  match exp_to_name "error direction" arg with
  | "super" ->
      Superset
  | "sub" ->
      Subset
  | "approx" ->
      Approxset
  | "exact" ->
      Exactset
  | _ ->
      raise
        (Error "[Dataflow] Unexpected error direction in set initialization.")

let get_time_unit (cid : Cid.t) : Z.t =
  match cid_to_name "time unit" cid with
  | "nanosec" ->
      Z.one
  | "microsec" ->
      Z.pow (Z.of_int 10) 3
  | "millisec" ->
      Z.pow (Z.of_int 10) 6
  | "sec" ->
      Z.pow (Z.of_int 10) 9
  | "min" ->
      Z.( * ) (Z.of_int 60) (Z.pow (Z.of_int 10) 9)
  | "hour" ->
      Z.( * ) (Z.of_int 3600) (Z.pow (Z.of_int 10) 9)
  | _ ->
      raise (Error "[Dataflow] Unexpected time unit in set initialization.")

let get_time_length (arg : exp) : Z.t =
  match arg.e with
  | ECall (cid, args) -> (
      check_num_args_df args 1 "time unit" ;
      let arg = List.hd args in
      match arg.e with
      | EInt (value, _) ->
          let time_unit = get_time_unit cid in
          Z.mul time_unit value
      | _ ->
          raise (Error "[Dataflow] unexpected time value in set initialization.")
      )
  | _ ->
      raise (Error "[Dataflow] Unexpected time value in set initialization.")

let is_positive (time : Z.t) : Z.t =
  if time <= Z.zero then
    raise (Error "[Dataflow] Expecting positive time parameter.")
  else if Z.log2 time >= Tofino.num_bit_in_ts then
    raise
      (Error
         "[Dataflow] Timestamp exceeding the maximum number of bits available."
      )
  else time

let is_nonnegative (time : Z.t) : Z.t =
  if time < Z.zero then
    raise (Error "[Dataflow] Expecting nonnegative time parameter.")
  else if Z.log2 time >= Tofino.num_bit_in_ts then
    raise
      (Error
         "[Dataflow] Timestamp exceeding the maximum number of bits available."
      )
  else time

let get_time_window (arg : exp) : time_fun =
  match arg.e with
  | ECall (cid, args) -> (
    match cid_to_name "time function" cid with
    | "within" ->
        check_num_args_df args 2 "time function" ;
        TWithin
          ( is_nonnegative (get_time_length (List.hd args))
          , is_positive (get_time_length (List.nth args 1)) )
    | "since" ->
        check_num_args_df args 1 "time function" ;
        TSince (is_positive (get_time_length (List.hd args)))
    | "last" ->
        check_num_args_df args 1 "time function" ;
        TLast (is_positive (get_time_length (List.hd args)))
    | _ ->
        raise
          (Error "[Dataflow] Unexpected time function in set initialization.") )
  | _ ->
      raise (Error "[Dataflow] Unexpected time window in set initialization.")

let check_state_ty (ty : ty) (userty_map : userty_map_ty) : raw_ty * string list
    =
  match ty.raw_ty with
  | TName (cid, [], true) -> (
      let raw_ty = get_userty cid userty_map in
      match raw_ty with
      | TRecord [(fst_field, TInt (IConst 32)); (snd_field, TInt (IConst 32))]
        ->
          (raw_ty, [fst_field; snd_field])
      | TRecord [(fst_field, TInt (IConst 32))] ->
          (raw_ty, [fst_field])
      | _ ->
          raise (Error "[Dataflow] Unexpected state type.") )
  | _ ->
      raise (Error "[Dataflow] Unexpected state type.")

(* Assumptions:
    1. Update function should have a record of either one or two int<32> fields
       as the return type and the second parameter type.
    2. The function body should have only one return statement.
       (No local variables)
*)
let prefix_state_var (state_param_opt : Id.t option) (pkt_param : Id.t)
    (fnames : string list) (cid : Cid.t) : Cid.t =
  let ids = Cid.to_ids cid in
  (* Cid.t has at least one Id. *)
  if Id.equal (List.hd ids) pkt_param then
    Cid.modify_head (fun _ -> Id.create "_p") cid
  else
    match state_param_opt with
    | Some state_param ->
        if Id.equal (List.hd ids) state_param then (
          check_num_items ids 2 "[Dataflow] Unexpected state variable." ;
          if List.hd fnames = Id.name (List.nth ids 1) then
            Cid.create ["_s"; "0"]
          else if
            List.length fnames = 2
            && List.nth fnames 1 = Id.name (List.nth ids 1)
          then Cid.create ["_s"; "1"]
          else raise (Error "[Dataflow] Unexpected state variable.") )
        else
          raise (Error "[Dataflow] Local variables should have been resolved.")
    | _ ->
        raise (Error "[Dataflow] Local variables should have been resolved.")

let prefix_vars_in_upd_body (state_param_opt : Id.t option) (pkt_param : Id.t)
    (fnames : string list) (fields : (string * exp) list) (fname : string) : exp
    =
  let rec prefix_vars_in_upd' (exp : exp) : exp =
    let e' =
      match exp.e with
      | EVal _ | EInt _ ->
          exp.e
      | EVar cid ->
          EVar (prefix_state_var state_param_opt pkt_param fnames cid)
      | EOp (op, args) ->
          EOp (op, List.map prefix_vars_in_upd' args)
      | ETernary (cond, e1, e2) ->
          let cond' = prefix_vars_in_upd' cond in
          let e1' = prefix_vars_in_upd' e1 in
          let e2' = prefix_vars_in_upd' e2 in
          ETernary (cond', e1', e2')
      | ECall (cid, args) ->
          raise (Error "[Dataflow] Unexpected ECall expression in the update.")
      | ERecord fields ->
          raise (Error "[Dataflow] Unexpected ERecord expression in the update.")
      | EWith _ ->
          raise (Error "[Dataflow] Unexpected EWith expression in the update.")
      | _ ->
          raise (Error "[Dataflow] Unexpected expression.")
    in
    {e= e'; ety= exp.ety; espan= exp.espan}
  in
  match get_from_fields fname fields with
  | Some exp ->
      prefix_vars_in_upd' exp
  | None ->
      raise (Error "[Dataflow] Unexpected return record field name.")

let rec exp_to_pred (exp : exp) : predicate =
  match exp.e with
  | EOp (Not, args) ->
      check_num_args_df args 1 "predicate" ;
      PredNot (exp_to_pred (List.hd args))
  | EOp (And, args) ->
      check_num_args_df args 2 "predicate" ;
      PredAnd (exp_to_pred (List.hd args), exp_to_pred (List.nth args 1))
  | EOp (Or, args) ->
      check_num_args_df args 2 "predicate" ;
      PredOr (exp_to_pred (List.hd args), exp_to_pred (List.nth args 1))
  | EOp (op, args) ->
      check_num_args_df args 2 "predicate" ;
      PredComp (op_to_compop op, List.hd args, List.nth args 1)
  | _ ->
      raise (Error "[Dataflow] Unexpected expression in predicate.")

let exp_to_upd (exp : exp) : update =
  match exp.e with
  | ETernary (cond, e1, e2) ->
      let pred = exp_to_pred cond in
      UpdTernary (pred, e1, e2)
  | EVal _ | EInt _ | EVar _ | EOp _ ->
      UpdExp exp
  | _ ->
      raise (Error "[Dataflow] Unexpected expression for update function.")

let rec get_update (upd_map : upd_map_ty) (upd_fun : exp) : update list =
  let fun_name =
    match upd_fun.e with
    | EVar (Id (name, _)) ->
        name
    | _ ->
        raise (error "[Dataflow] Unexpected second argument of fold function.")
  in
  match StrMap.find_option upd_map fun_name with
  | Some updates ->
      updates
  | _ ->
      raise (error "[Dataflow] Undefined update function.")

let get_query_fun (upd_map : upd_map_ty) (set_class : string) (exp : exp) :
    query_fun =
  match (set_class, exp.e) with
  | "ExistSet", ECall (Id ("Exist", _), []) ->
      QExist
  | "CountSet", ECall (Id ("Count", _), []) ->
      QCount
  | "FoldSet", ECall (Id ("Fold", _), args) -> (
      check_num_args_df args 3 "fold function" ;
      let init_vals = List.hd args |> get_update upd_map in
      let upd_vals = List.nth args 1 |> get_update upd_map in
      let res_idx = List.nth args 2 in
      if List.length init_vals <> List.length upd_vals then
        raise (Error "[Dataflow] Unmatched number of fields in fold functions.") ;
      match res_idx.e with
      | EInt (z, _) ->
          let idx = Z.to_int z in
          if idx >= List.length init_vals then
            raise
              (Error
                 "[Dataflow] Index exceeds number of fields in fold function."
              )
          else QFold (init_vals, upd_vals, idx)
      | _ ->
          raise (Error "[Dataflow] Unexpected result index in fold function.") )
  | _, _ ->
      raise (Error "[Dataflow] Unexpected set class.")

let in_valid_set_class (comp : Cid.t -> bool) (suffix : string) : bool =
  let set_classes = ["ExistSet"; "CountSet"; "FoldSet"] in
  let results =
    List.map
      (fun set_class -> comp (Cid.create [set_class; suffix]))
      set_classes
  in
  List.fold_left ( || ) false results

let preproc_decls (prog : decl list) : Id.t * statement list * set_map_ty =
  let (userty_map : userty_map_ty) = StrMap.create (List.length prog) in
  let (set_map : set_map_ty) = StrMap.create (List.length prog) in
  let (upd_map : upd_map_ty) = StrMap.create (List.length prog) in
  let preproc_decl (decl : decl) :
      raw_ty option * (Id.t * statement list) option =
    match decl.d with
    | DUserTy (id, _, ty) ->
        StrMap.replace userty_map (Id.name id) ty.raw_ty ;
        (None, None)
    | DFun (id, ret_ty_name, ctrl_spec, (params, s)) -> (
        let ret_ty, fnames = check_state_ty ret_ty_name userty_map in
        if List.length params > 2 || List.length params = 0 then
          raise
            (Error
               "[Dataflow] Expecting either one or two parameters in the \
                function." )
        else
          let pkt_param, pkt_ty = List.hd params in
          let state_param_opt =
            if List.length params = 2 then (
              let state_param, state_ty_name = List.nth params 1 in
              let state_ty, _ = check_state_ty state_ty_name userty_map in
              if ret_ty <> state_ty then
                raise
                  (Error
                     "[Dataflow] Unexpected return and state type in the \
                      function." ) ;
              if pkt_param = state_param then
                raise
                  (Error "[Dataflow] Parameters should have different names.") ;
              Some state_param )
            else (* List.length params = 1 *) None
          in
          let ss = flatten_stmt s |> List.filter (fun s -> s.s <> SNoop) in
          match ss with
          | [{s= SRet (Some {e= ERecord fields})}] ->
              let updates =
                List.map
                  (prefix_vars_in_upd_body state_param_opt pkt_param fnames
                     fields )
                  fnames
                |> List.map exp_to_upd
              in
              StrMap.replace upd_map (Id.name id) updates ;
              (Some pkt_ty.raw_ty, None)
          | _ ->
              raise (Error "[Dataflow] Unexpected function body.") )
    | DGlobal (id, ty, exp) -> (
      match (ty.raw_ty, exp.e) with
      | TName (cid1, sizes, true), ECall (cid2, args) ->
          if
            in_valid_set_class (Cid.equal_names cid1) "t"
            && in_valid_set_class (Cid.equal_names cid2) "create"
          then (
            let set_class_1 = Id.name (Cid.first_id cid1) in
            let set_class_2 = Id.name (Cid.first_id cid2) in
            if set_class_1 <> set_class_2 then
              raise (Error "[Dataflow] Unmatched set classes") ;
            check_num_args_df args 3 "set initialization" ;
            check_num_items sizes 1
              "[Dataflow] Expecting exactly one size argument." ;
            match List.hd sizes with
            | IUser cid3 ->
                let keys_ty = get_userty cid3 userty_map in
                let err = get_err (List.hd args) in
                let time_win = get_time_window (List.nth args 1) in
                let query_fun =
                  List.nth args 2 |> get_query_fun upd_map set_class_1
                in
                StrMap.replace set_map (Id.name id)
                  (keys_ty, err, time_win, query_fun) ;
                (None, None)
            | _ ->
                raise (Error "[Dataflow] Unexpected size argument.") )
          else
            raise
              (Error "[Dataflow] Expecting only global declarations of sets.")
      | _ ->
          raise (Error "[Dataflow] Expecting only global declarations of sets.")
      )
    | DHandler (_, _, (params, s)) ->
        check_num_items params 1
          "[Dataflow] Expecting exactly one parameter in the handler." ;
        let pkt_param, pkt_ty = List.hd params in
        (Some pkt_ty.raw_ty, Some (pkt_param, flatten_stmt s))
    | _ ->
        raise (Error "[Dataflow] Unexpected declaration.")
  in
  let pkt_ty_list, preproc_results = List.split (List.map preproc_decl prog) in
  let pkt_ty_list = list_uniq (List.filter_map (fun x -> x) pkt_ty_list) in
  let preproc_results = List.filter_map (fun x -> x) preproc_results in
  check_num_items pkt_ty_list 1 "[Dataflow] Expecting exactly one packet type." ;
  check_num_items preproc_results 1
    "[Dataflow] Expecting exactly one handler declaration." ;
  let preproc_result = List.hd preproc_results in
  (fst preproc_result, snd preproc_result, set_map)

(* Assumptions:
   1. Checker needs to add width to Eint using key.
   2. Every cid's type has been checked with keys_ty i.e. the record type. *)
let exp_to_key (position : string) (exp : exp) : e =
  match exp.e with
  | EVar _ | EInt (_, Some (IConst _)) ->
      exp.e
  | EInt (_, None) ->
      raise
        (Error
           ("[Dataflow] Int width should have been resolved in" ^ position ^ ".")
        )
  | _ ->
      raise (Error ("[Dataflow] Unexpected key in" ^ position ^ "."))

let preproc_branches (match_keys : exp list) (bs : branch list)
    (set_map : set_map_ty) : dag_stmt option =
  let num_match_keys = List.length match_keys in
  let preproc_branch (b : branch) :
      (* res_var * query_fun_str * set_name * pattern list * api * keys *)
      (cid option * string option * string option * pat list * api * e list)
      option
      * (pat list * dag_stmt list) option =
    let pats, s = b in
    check_num_items pats num_match_keys
      "[Dataflow] Expecting the same number of match patterns as match keys." ;
    let ss = flatten_stmt s |> List.filter (fun s -> s.s <> SNoop) in
    if List.length ss = 0 then
      (Some (None, None, None, pats, AClear, []), Some (pats, []))
    else
      let first_stmt = List.hd ss in
      match first_stmt.s with
      | SUnit {e= ECall (cid, args)} ->
          check_num_items ss 1
            "[Dataflow] Expecting exactly one set operation in a match branch." ;
          if in_valid_set_class (Cid.equal_names cid) "add" then (
            let query_fun_str = Id.name (Cid.first_id cid) in
            check_num_args_df args 2 "set insertion" ;
            let set_name = exp_to_name "set insertion" (List.hd args) in
            match (List.nth args 1).e with
            | ERecord fields ->
                let keys =
                  List.map
                    (fun (_, key) -> exp_to_key "set insertion" key)
                    fields
                in
                ( Some
                    ( None
                    , Some query_fun_str
                    , Some set_name
                    , pats
                    , AInsert
                    , keys )
                , None )
            | _ ->
                raise (Error "[Dataflow] Unexpected argument in set insertion.")
            )
          else
            raise
              (Error "[Dataflow] Unexpected ECall statement in match branch.")
      | SUnit _ ->
          raise (Error "[Dataflow] Unexpected SUnit statement in match branch.")
      | SAssign (cid1, exp) -> (
        match exp.e with
        | ECall (cid2, args) -> (
            check_num_items ss 1
              "[Dataflow] Expecting exactly one set operation in a match \
               branch." ;
            let query_names = Cid.names cid2 in
            check_num_items query_names 2 "[Dataflow] Unexpected query method." ;
            let query_fun_str = List.hd query_names in
            let api =
              match List.nth query_names 1 with
              | "add_query" ->
                  AInsQuery
              | "query" ->
                  AQuery
              | _ ->
                  raise (Error "[Dataflow] Unexpected query method.")
            in
            check_num_args_df args 2 "set querying" ;
            let set_name = exp_to_name "set querying" (List.hd args) in
            match (List.nth args 1).e with
            | ERecord fields ->
                let keys =
                  List.map
                    (fun (_, key) -> exp_to_key "set querying" key)
                    fields
                in
                ( Some
                    ( Some cid1
                    , Some query_fun_str
                    , Some set_name
                    , pats
                    , api
                    , keys )
                , None )
            | _ ->
                raise (Error "[Dataflow] Unexpected argument in set querying.")
            )
        | _ ->
            let not_set_stmt (s : statement) =
              match s.s with
              | SAssign (_, {e= ECall _}) ->
                  None
              | SAssign (cid, exp) ->
                  Some (DSAssign (cid, exp))
              | SNoop ->
                  raise (Error "[Dataflow] SNoop should have been removed.")
              | SUnit _ ->
                  None (* Set operations *)
              | SLocal _ ->
                  raise
                    (Error "[Dataflow] SLocal not allowed in match branches.")
              | SMatch _ ->
                  raise (Error "[Dataflow] Match statements cannot be nested")
              | _ ->
                  raise (Error "[Dataflow] Unexpected statements.")
            in
            let ss_filtered = List.filter_map not_set_stmt ss in
            if List.length ss <> List.length ss_filtered then
              raise
                (Error
                   "[Dataflow] Unexpected mixture of set operations and \
                    non-set operations in a match branch." )
            else (None, Some (pats, ss_filtered)) )
      | SNoop ->
          raise (Error "[Dataflow] SNoop should have been removed.")
      | SLocal _ ->
          raise (Error "[Dataflow] SLocal not allowed in match branches.")
      | SMatch _ ->
          raise (Error "[Dataflow] Match statements cannot be nested")
      | _ ->
          raise (Error "[Dataflow] Unexpected statements.")
  in
  let bs_results = List.map preproc_branch bs in
  let set_bs = List.filter_map fst bs_results in
  let not_set_bs = List.filter_map snd bs_results in
  let both_bs_len =
    List.length
      (List.filter_map
         (fun (set_b, non_set_b) ->
           match (set_b, non_set_b) with
           | Some _, Some _ ->
               Some set_b
           | _, _ ->
               None )
         bs_results )
  in
  (* Remove match statement with all empty branches *)
  if both_bs_len = List.length bs_results then None
  else if
    List.length set_bs = List.length bs_results
    && List.length not_set_bs = both_bs_len
  then (
    let result_vars =
      List.filter_map (fun (x, _, _, _, _, _) -> x) set_bs |> list_uniq
    in
    check_num_items result_vars 1
      "[Dataflow] Expecting exactly one result variable for all set operations \
       in a match statement." ;
    let query_fun_str_list =
      List.filter_map (fun (_, x, _, _, _, _) -> x) set_bs |> list_uniq
    in
    check_num_items query_fun_str_list 1
      "[Dataflow] Expecting exactly one query function for all set operations \
       in a match statement." ;
    let set_names =
      List.filter_map (fun (_, _, x, _, _, _) -> x) set_bs |> list_uniq
    in
    check_num_items set_names 1
      "[Dataflow] Expecting exactly one set for all set operations in a match \
       statement." ;
    let res_var = List.hd result_vars in
    let query_fun_str = List.hd query_fun_str_list in
    let set_name = List.hd set_names in
    let new_bs =
      List.map (fun (_, _, _, pats, api, keys) -> (pats, api, keys)) set_bs
    in
    let last_pat, _, _ = List.nth new_bs (List.length new_bs - 1) in
    let wild_pat = list_repeat (List.length last_pat) PWild in
    let new_bs_extended =
      if last_pat <> wild_pat then new_bs @ [(wild_pat, AClear, [])] else new_bs
    in
    match StrMap.find_option set_map set_name with
    | Some (keys_ty, err, time_fun, query_fun) -> (
        StrMap.remove set_map set_name ;
        match (query_fun_str, query_fun) with
        | "ExistSet", QExist | "CountSet", QCount | "FoldSet", QFold _ ->
            Some
              (DSDataStruct
                 { set_name
                 ; res_var
                 ; keys_ty
                 ; err
                 ; time_fun
                 ; query_fun
                 ; match_keys
                 ; branches= new_bs_extended } )
        | _ ->
            raise (Error "[Dataflow] Unmatched set classes.") )
    | None ->
        raise (Error "[Dataflow] Set undeclared.") )
  else if
    List.length set_bs = both_bs_len
    && List.length not_set_bs = List.length bs_results
  then
    let last_pat, _ = List.nth not_set_bs (List.length not_set_bs - 1) in
    let wild_pat = list_repeat (List.length last_pat) PWild in
    let not_set_bs_extended =
      if last_pat <> wild_pat then not_set_bs @ [(wild_pat, [])] else not_set_bs
    in
    Some (DSMatch (match_keys, not_set_bs_extended))
  else
    raise
      (Error
         "[Dataflow] Unexpected mixture of set operations and non-set \
          operations in a match statement." )

let prefix_local_var (set_map : set_map_ty) (pkt_param : Id.t) (cid : Cid.t) :
    Cid.t =
  let md_prefix = Cid.create_ids [Id.create "_p"; Id.create "meta"] in
  let first_id = Cid.first_id cid in
  if Id.equal first_id pkt_param then
    Cid.modify_head (fun _ -> Id.create "_p") cid
  else
    match StrMap.find_option set_map (Id.name first_id) with
    | Some _ ->
        cid
    | None ->
        Cid.concat md_prefix cid

(* Assumptions:
    1. All (EVar cids) are either local variables (i.e. SLocal) or global variables
      (i.e. set names in DGlobal).
    2. Copy by values during SAssign. *)
let prefix_vars_in_exp (set_map : set_map_ty) (pkt_param : Id.t) (exp : exp) :
    exp =
  let rec prefix_vars_in_exp' (exp : exp) : exp =
    let e' =
      match exp.e with
      | EVal _ | EInt _ ->
          exp.e
      | EVar cid ->
          EVar (prefix_local_var set_map pkt_param cid)
      | EOp (op, args) ->
          EOp (op, List.map prefix_vars_in_exp' args)
      | ECall (cid, args) ->
          ECall (cid, List.map prefix_vars_in_exp' args)
      | ERecord fields ->
          ERecord
            (List.map
               (fun (name, exp) -> (name, prefix_vars_in_exp' exp))
               fields )
      | EWith _ ->
          raise (Error "[Dataflow] EWith expression should have been resolved.")
      | _ ->
          raise (Error "[Dataflow] Unexpected expression.")
    in
    {e= e'; ety= exp.ety; espan= exp.espan}
  in
  prefix_vars_in_exp' exp

let preproc_stmts (ss : statement list) (set_map : set_map_ty) (pkt_param : Id.t)
    : dag_stmt list =
  let rec prefix_vars_in_stmt (s : statement) : statement =
    let s' =
      match s.s with
      | SUnit e ->
          SUnit (prefix_vars_in_exp set_map pkt_param e)
      | SLocal (cid, t, e) ->
          Printf.printf "%s\n" (Cid.to_string cid) ;
          SLocal
            ( prefix_local_var set_map pkt_param cid
            , t
            , prefix_vars_in_exp set_map pkt_param e )
      | SAssign (cid, e) ->
          Printf.printf "%s\n" (Cid.to_string cid) ;
          SAssign
            ( prefix_local_var set_map pkt_param cid
            , prefix_vars_in_exp set_map pkt_param e )
      | SMatch (match_keys, bs) ->
          SMatch
            ( List.map (prefix_vars_in_exp set_map pkt_param) match_keys
            , List.map (fun (pats, b_s) -> (pats, prefix_vars_in_stmt b_s)) bs
            )
      | SSeq (s1, s2) ->
          SSeq (prefix_vars_in_stmt s1, prefix_vars_in_stmt s2)
      | _ ->
          s.s
    in
    {s= s'; sspan= s.sspan; noinline= s.noinline}
  in
  let preproc_branches_in_stmt (s : statement) : dag_stmt option =
    match s.s with
    | SNoop ->
        None
    | SUnit e ->
        raise
          (Error
             "[Dataflow] Unexpected SUnit statements outside SMatch statements."
          )
    | SLocal (cid, t, e) ->
        Some (DSLocal (cid, t, e))
    | SAssign (cid, e) ->
        Some (DSAssign (cid, e))
    | SMatch (match_keys, bs) ->
        preproc_branches match_keys bs set_map
    | _ ->
        raise (Error "[Dataflow] Unexpected statement.")
  in
  List.filter_map preproc_branches_in_stmt (List.map prefix_vars_in_stmt ss)

let rec get_read_var_from_expr (exp : exp) : Cid.t list =
  match exp.e with
  | EVal _ | EInt _ ->
      []
  | EVar cid ->
      [cid]
  | EOp (op, args) ->
      List.map get_read_var_from_expr args |> List.flatten
  | ECall _ ->
      raise (Error "[Dataflow] Unexpected ECall expression.")
  | ERecord _ ->
      raise (Error "[Dataflow] Unexpected ERecord expression.")
  | EWith _ ->
      raise (Error "[Dataflow] Unexpected EWith expression.")
  | _ ->
      raise (Error "[Dataflow] Unexpected expressions.")

let rec get_read_var_from_pred (p : predicate) : Cid.t list =
  match p with
  | PredAnd (p1, p2) | PredOr (p1, p2) ->
      get_read_var_from_pred p1 @ get_read_var_from_pred p2
  | PredComp (_, e1, e2) ->
      get_read_var_from_expr e1 @ get_read_var_from_expr e2
  | PredNot p1 ->
      get_read_var_from_pred p1

(* TODO *)
let expr_allowed_in_reg (exp : exp) : unit = ()

let pred_allowed_in_reg (pred : predicate) : unit = ()

let get_read_var_from_update (keep_state_var : bool) (u : update) : Cid.t list =
  let get_read_var_from_update' (u : update) =
    match u with
    | UpdExp e ->
        expr_allowed_in_reg e ; get_read_var_from_expr e
    | UpdTernary (cond, e1, e2) ->
        pred_allowed_in_reg cond ;
        expr_allowed_in_reg e1 ;
        expr_allowed_in_reg e2 ;
        get_read_var_from_pred cond
        @ get_read_var_from_expr e1 @ get_read_var_from_expr e2
  in
  let not_state_var (id : Cid.t) =
    match Id.name (Cid.first_id id) with "_s" -> false | _ -> true
  in
  if keep_state_var then get_read_var_from_update' u
  else List.filter not_state_var (get_read_var_from_update' u)

let get_read_var_from_query_fun (keep_state_var : bool) (query_fun : query_fun)
    =
  let agg_var =
    match query_fun with
    (* | AggCountDist ids ->
        get_read_var_from_idents ids *)
    | QFold (inits, upds, _) ->
        List.flatten (List.map (get_read_var_from_update keep_state_var) inits)
        @ List.flatten (List.map (get_read_var_from_update keep_state_var) upds)
    | _ ->
        []
  in
  agg_var

(* Assumptions:
   1. match key expressions should have been moved to SAssign.
*)
let get_read_var (s : dag_stmt) : Cid.t list =
  let rec get_read_var' s =
    match s with
    | DSUnit e | DSLocal (_, _, e) | DSAssign (_, e) ->
        get_read_var_from_expr e
    | DSMatch (match_keys, bs) ->
        let get_read_var_from_branch ((_, ss) : dag_branch) =
          List.flatten (List.map get_read_var' ss)
        in
        List.map (exp_to_cid "match keys") match_keys
        @ List.flatten (List.map get_read_var_from_branch bs)
    | DSDataStruct {match_keys; branches; query_fun} ->
        let get_read_var_from_branch ((_, _, keys) : set_branch) =
          let get_read_var_from_key (key : e) =
            match key with EVar cid -> Some cid | _ -> None
          in
          List.filter_map get_read_var_from_key keys
        in
        List.map (exp_to_cid "match keys") match_keys
        @ List.flatten (List.map get_read_var_from_branch branches)
        @ get_read_var_from_query_fun false query_fun
    | DSNoop ->
        raise (Error "[Dataflow] SNoop should have been removed.")
  in
  list_uniq (get_read_var' s)

let get_write_var (s : dag_stmt) : Cid.t list =
  let rec get_write_var' s =
    match s with
    | DSUnit _ ->
        []
    | DSLocal (cid, _, _) | DSAssign (cid, _) ->
        [cid]
    | DSMatch (match_keys, bs) ->
        let get_write_var_from_branch ((_, ss) : dag_branch) =
          List.flatten (List.map get_write_var' ss)
        in
        List.flatten (List.map get_write_var_from_branch bs)
    | DSDataStruct {res_var} ->
        [res_var]
    | DSNoop ->
        raise (Error "[Dataflow] SNoop should have been removed.")
  in
  list_uniq (get_write_var' s)

let rec find_edge_r_w r_w_s root =
  let rec find_most_recent_r_before_w w s rest_r_w_s =
    match rest_r_w_s with
    | (r_prev, _, s_prev) :: tl ->
        if List.exists (fun wvar -> List.mem wvar r_prev) w then
          (s_prev, 0, s) :: find_most_recent_r_before_w w s tl
          (* Find out r's -> w *)
        else find_most_recent_r_before_w w s tl
    | [] ->
        [(root, 1, s)]
  in
  match r_w_s with
  | (r, w, s) :: tl ->
      find_most_recent_r_before_w w s tl @ find_edge_r_w tl root
  | [] ->
      []

let rec find_edge_w_w r_w_s root =
  let rec find_most_recent_w_before_w w s rest_r_w_s =
    match rest_r_w_s with
    | (_, w_prev, s_prev) :: tl ->
        if List.exists (fun wvar -> List.mem wvar w_prev) w then (s_prev, 2, s)
        else find_most_recent_w_before_w w s tl
    | [] ->
        (root, 1, s)
  in
  match r_w_s with
  | (r, w, s) :: tl ->
      find_most_recent_w_before_w w s tl :: find_edge_w_w tl root
  | [] ->
      []

let rec find_edge_w_r r_w_s root =
  let rec find_most_recent_w_before_r r s rest_r_w_s =
    match rest_r_w_s with
    | (_, w_prev, s_prev) :: tl ->
        if List.exists (fun wvar -> List.mem wvar w_prev) r then (s_prev, 1, s)
        else find_most_recent_w_before_r r s tl
    | [] ->
        (root, 1, s)
  in
  match r_w_s with
  | (r, w, s) :: tl ->
      find_most_recent_w_before_r r s tl :: find_edge_w_r tl root
  | [] ->
      []

let print_r_w_n rwn_list : unit =
  let print_one_pair ((r, w, n) : Cid.t list * Cid.t list * StNode.t) =
    let string_of_list_ident vs =
      String.concat ", " (List.map Cid.to_string vs)
    in
    Printf.printf "\t%n: [%s], [%s]\n%!" n.StNode.id (string_of_list_ident r)
      (string_of_list_ident w)
  in
  let _ = List.map print_one_pair rwn_list in
  ()

(* Assumptions:
    1. SVariable = 0 for all local variables used in the programs, in the very beginning *)
let to_df_dag (p : decl list) : int * StNode.t * StG.t =
  let t0 = Sys.time () in
  let pkt_param, ss, set_map = preproc_decls p in
  let dag_ss = preproc_stmts ss set_map pkt_param in
  let gen_rw_vars (n : StNode.t) =
    let read_vars = get_read_var n.s in
    let write_vars = get_write_var n.s in
    (read_vars, write_vars, n)
  in
  let root = {StNode.id= 0; s= DSNoop} in
  let max_id = List.length dag_ss in
  let _, nodes =
    List.fold_right
      (fun s (i, agg) -> (i - 1, {StNode.id= i; s} :: agg))
      dag_ss (max_id, [])
  in
  let r_w_n = List.map gen_rw_vars nodes in
  let rev_r_w_n = List.rev r_w_n in
  Printf.printf "[Dataflow] Read and write variables:\n" ;
  print_r_w_n rev_r_w_n ;
  let df_dag = StG.create ~size:(List.length nodes) () in
  let add_edges = List.fold_left (fun _ e -> StG.add_edge_e df_dag e ; ()) () in
  StG.add_vertex df_dag root ;
  List.fold_left (fun _ s -> StG.add_vertex df_dag s ; ()) () nodes ;
  add_edges (find_edge_r_w rev_r_w_n root) ;
  add_edges (find_edge_w_w rev_r_w_n root) ;
  add_edges (find_edge_w_r rev_r_w_n root) ;
  let t1 = Sys.time () in
  Printf.printf "[Dataflow] Edges in the dataflow graph:\n" ;
  print_df_dag df_dag ;
  Printf.printf "[Dataflow] Time to create the DAG: %.8fs\n" (t1 -. t0) ;
  (max_id, root, df_dag)
