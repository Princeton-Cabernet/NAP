open Syntax
open SetIR
open Printing

let string_of_api (api : api) =
  match api with
  | AInsert ->
      "Insert"
  | AQuery ->
      "Query"
  | AInsQuery ->
      "InsQuery"
  | AClear ->
      "Clear"

let string_of_api_set (api_set : api_set) =
  match api_set with
  | ASQ ->
      "Q"
  | ASI ->
      "I"
  | ASInQ ->
      "InQ"
  | ASIQ ->
      "IQ"
  | ASIInQ ->
      "IInQ"
  | ASQInQ ->
      "QInQ"
  | ASIQInQ ->
      "IQInQ"

let string_of_time (time : time_fun) =
  match time with
  | TWithin (lo, hi) ->
      Printf.sprintf "Within %s %s" (Z.to_string lo) (Z.to_string hi)
  | TSince t ->
      Printf.sprintf "Since %s" (Z.to_string t)
  | TLast t ->
      Printf.sprintf "Last %s" (Z.to_string t)

let string_of_query (query : query_fun) =
  match query with QExist -> "Exist" | QCount -> "Count" | QFold _ -> "Fold"

(* let string_of_key (key : key_ty) =
   match key with KInt i -> Integer.to_p4_string i | KVar v -> Cid.to_string v *)

let string_of_set_branch ((pats, api, keys) : set_branch) =
  Printf.sprintf "[%s] -> (%s, [%s])"
    (String.concat "," (List.map pat_to_string pats))
    (string_of_api api)
    (String.concat "," (List.map e_to_string keys))

let rev_inequality (op : compop) =
  match op with
  | PLt ->
      PGt
  | PGt ->
      PLt
  | PLe ->
      PGe
  | PGe ->
      PLe
  | PEq | PNotEq ->
      op
(* | ApxEq -> op *)

let inv_comp_op (op : compop) =
  match op with
  | PLt ->
      PGe
  | PGt ->
      PLe
  | PLe ->
      PGt
  | PGe ->
      PLt
  | PEq ->
      PNotEq
  | PNotEq ->
      PEq
(* | ApxEq  -> ApxEq  *)

let op_to_compop (op : op) : compop =
  match op with
  | Less ->
      PLt
  | More ->
      PGt
  | Leq ->
      PLe
  | Geq ->
      PGe
  | Eq ->
      PEq
  | Neq ->
      PNotEq
  | _ ->
      raise (Error "[Dataflow] Unexpected operator in predicate.")

let compop_to_op (op : compop) : op =
  match op with
  | PLt ->
      Less
  | PGt ->
      More
  | PLe ->
      Leq
  | PGe ->
      Geq
  | PEq ->
      Eq
  | PNotEq ->
      Neq
