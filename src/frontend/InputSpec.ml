open Collections
open MiscUtils

let input_spec_map =
  let map = StrMap.create 10 in
  StrMap.replace map "2/dist_count" (Z.of_int 60000000000, 57060.) ;
  StrMap.replace map "3/dist_count" (Z.of_int 60000000000, 57060.) ;
  StrMap.replace map "4/dist_count" (Z.of_int 60000000000, 57060.) ;
  StrMap.replace map "5/dist_count" (Z.of_int 60000000000, 57060.) ;
  StrMap.replace map "6/dist_count" (Z.of_int 60000000000, 57060.) ;
  StrMap.replace map "8/dist_count" (Z.of_int 60000000000, 57060.) ;
  StrMap.replace map "10/dist_count" (Z.of_int 60000000000, 57060.) ;
  map

(* the keys are not unique: missing the conditions for insertion. *)
(* 150335.78 *)
