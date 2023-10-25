open Syntax
open MiscUtils
open SetIR
open DagIR
open P4IR
open Collections

type time_map = (Z.t * int * int) TimeMap.t

type dstime_set = unit DSMap.t

type syninfo =
  { set_name: string
  ; keys_ty: raw_ty
  ; time_fun: time_fun
  ; query_fun: query_fun
  ; match_keys: exp list
  ; branches: set_branch list
  ; has_clear_branch: bool
  ; api_set: api_set }

type sketch_opt_rec =
  {num_dist_keys: int; num_apis: int; num_reg_progs: int (* ; qweight: float *)}

type fold_opt_rec =
  { num_dist_keys: int
  ; num_apis: int
  ; num_reg_progs: int (* ; qweight: float *)
  ; err: err
  ; num_entries: int
  ; key_length: int }

type sketch_alloc_rec = {w: int; r: int; block: int; num_slot_log2: int}

type fold_alloc_rec =
  { w: int
  ; r: int
  ; block: int
  ; num_slot_log2: int
  ; num_32b_fp: int
  ; timestamp: bool }

type optinfo =
  | OptBloom of sketch_opt_rec
  | OptCMS of sketch_opt_rec
  | OptFold of fold_opt_rec

type allocinfo =
  | AllocBloom of sketch_alloc_rec
  | AllocCMS of sketch_alloc_rec
  | AllocFold of fold_alloc_rec

(* TRUE -> later stages; FALSE -> same or later stages *)
(* TRUE -> recursive; FALSE -> single merge *)
type nodetyp =
  | Hash of bool
  | Table of bool
  | Atom of bool
  | Clear of (bool * bool)
  | Reg of bool
(* Clear of int | Hash of int | API | Reg of bool | Merge | Cap | Other *)

type res_node =
  { typ: nodetyp
  ; num_tbl: int
  ; num_act: int
  ; num_hash: int
  ; num_reg: int
  ; num_block: int }

module type DS = sig
  type opt_rec

  type alloc_rec

  val get_alloc : (int * int) list -> allocinfo list

  val get_block_slot_pairs : opt_rec -> int -> int -> (int * int) list

  val add_block : (int * int) list -> opt_rec -> alloc_rec -> allocinfo list

  val get_utility :
    int -> Z.t -> int -> syninfo -> opt_rec -> alloc_rec -> input_map -> float

  val get_res_nodes :
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
    -> res_node list

  val get_res_nodes_and_p4 :
       string
    -> int
    -> int
    -> int
    -> int
    -> int
    -> int
    -> Z.t
    -> int
    -> cid
    -> bool
    -> syninfo
    -> opt_rec
    -> alloc_rec
    -> (res_node list * code_type) list
end

type pred_comp = compop * exp * exp

type pred_seed = PSeedTrue | PSeedFalse | PSeedSimp of pred_comp

type pred_name =
  | PNameTrue
  | PNameFalse
  | PNameInt of int
  | PNameNot of int
  | PNameAnd of pred_name * pred_name
  | PNameOr of pred_name * pred_name

module PSeedKey = struct
  (* id * w *)
  type t = pred_comp

  let equal (i : t) (j : t) = i = j

  let hash (i : t) = Hashtbl.hash i
end

module PSeedMap = Hashtbl.Make (PSeedKey)

module PNameKey = struct
  (* id * w *)
  type t = pred_name

  let equal (i : t) (j : t) = i = j

  let hash (i : t) = Hashtbl.hash i
end

module PNameMap = Hashtbl.Make (PNameKey)
