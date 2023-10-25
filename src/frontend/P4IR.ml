type cat_match =
  | MMatch of Syntax.pat
  | MIdent of Cid.t
  | MRange of (Cid.t * Cid.t)

type cat_entry = MkCatEntry of cat_match list * string * Syntax.exp list

type cat_action =
  | MkCatAction of string * (Syntax.ty * string) list * DagIR.dag_stmt list

type cat_table =
  | MkCatTable of string * Syntax.exp list * string list * cat_entry list

(* *)
type prog_tuple =
  Petr4.P4light.coq_Declaration list
  * Petr4.P4light.coq_DeclarationField list
  * Petr4.P4light.coq_Declaration list
  * Petr4.P4light.coq_Declaration list
  * Petr4.P4light.coq_StatementPreT list

type param_tuple = Petr4.P4light.direction * Petr4.P4light.coq_P4Type * string

let empty_prog_tuple : prog_tuple = ([], [], [], [], [])

type code_type =
  | CodeP4 of prog_tuple
  | CodeTable of cat_table * cat_action list
  | CodeCtrlBegin of string * param_tuple list
  | CodeCtrlEnd of prog_tuple

let union_prog_tuple ((a1, b1, c1, d1, e1) : prog_tuple)
    ((a2, b2, c2, d2, e2) : prog_tuple) : prog_tuple =
  (a1 @ a2, b1 @ b2, c1 @ c2, d1 @ d2, e1 @ e2)
