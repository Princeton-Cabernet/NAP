open Syntax
open MiscUtils
open Graph
open SetIR

type setinfo =
  { set_name: string
  ; res_var: cid
  ; keys_ty: raw_ty
  ; err: err
  ; time_fun: time_fun
  ; query_fun: query_fun
  ; match_keys: exp list
  ; branches: set_branch list }

type dag_stmt =
  | DSNoop
  | DSUnit of exp
  | DSLocal of cid * ty * exp
  | DSAssign of cid * exp
  | DSMatch of exp list * dag_branch list
  | DSDataStruct of setinfo

and dag_branch = pat list * dag_stmt list

module StNode = struct
  type t = {id: int; s: dag_stmt}

  let compare n1 n2 = Stdlib.compare n1.id n2.id

  let hash n = Hashtbl.hash n.id

  let equal n1 n2 = n1.id = n2.id
end

module StEdge = struct
  type t = int

  let compare = Stdlib.compare

  let equal = ( = )

  (* 2: w -> w; 1: w -> r; 0: r -> w *)
  let default = 1
end

module StG = Graph.Imperative.Digraph.ConcreteLabeled (StNode) (StEdge)

let print_df_dag (dag : StG.t) : unit =
  let print_edge e =
    Printf.printf "\t( %d: %d -> %d )\n" (StG.E.label e) (StG.E.src e).id
      (StG.E.dst e).id
  in
  StG.iter_edges_e print_edge dag
