open Syntax

type err = Superset | Subset | Approxset | Exactset

type api = AInsert | AQuery | AInsQuery | AClear

type api_set = ASQ | ASI | ASInQ | ASIQ | ASIInQ | ASQInQ | ASIQInQ

type compop = PLt | PGt | PLe | PGe | PEq | PNotEq

type predicate =
  | PredNot of predicate
  | PredAnd of predicate * predicate
  | PredOr of predicate * predicate
  | PredComp of compop * exp * exp

type update = UpdExp of exp | UpdTernary of predicate * exp * exp

type query_fun = QExist | QCount | QFold of update list * update list * int

type time_fun = TWithin of Z.t * Z.t | TSince of Z.t | TLast of Z.t

(* type key_ty = KInt of zint | KVar of cid *)

type set_branch = pat list * api * e list

type tframe_ty = Sliding | Tumbling
