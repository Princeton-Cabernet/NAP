open Batteries
open Syntax
open SetIR
open DagIR
(* module IdMap = Map.Make (Id)
   let idmap_to_string f map =
     "{ "
     ^ IdMap.fold
         (fun k v acc -> Id.to_string k ^ " -> " ^ f v ^ "; " ^ acc)
         map ""
     ^ " }"
      module CidMap = Map.Make (Cid)
      module StringMap = Map.Make (String)
      module IdSet = Set.Make (Id)
      module CidSet = Set.Make (Cid)
      module StringSet = Set.Make (String) *)

module TimeWinKey = struct
  (* tframetype * id * w *)
  type t = tframe_ty * int * int

  let equal (i : t) (j : t) = i = j

  let hash (i : t) = Hashtbl.hash i
end

module TimeMap = Hashtbl.Make (TimeWinKey)

module IntKey = struct
  type t = int

  let equal (i : t) (j : t) = i = j

  let hash (i : t) = Hashtbl.hash i
end

module IntMap = Hashtbl.Make (IntKey)

module StmtsKey = struct
  type t = dag_stmt list

  let equal (i : t) (j : t) = i = j

  let hash (i : t) = Hashtbl.hash i
end

module StmtsMap = Hashtbl.Make (StmtsKey)

module StrKey = struct
  type t = string

  let equal (i : t) (j : t) = i = j

  let hash (i : t) = Hashtbl.hash i
end

module StrMap = Hashtbl.Make (StrKey)

type input_map = (Z.t * float) StrMap.t

module IdKey = struct
  type t = id

  let equal (i : t) (j : t) = i = j

  let hash (i : t) = Hashtbl.hash i
end

module IdMap = Hashtbl.Make (IdKey)

module CidKey = struct
  type t = cid

  let equal (i : t) (j : t) = i = j

  let hash (i : t) = Hashtbl.hash i
end

module CidMap = Hashtbl.Make (CidKey)

module DSKey = struct
  (* tframetype * id *)
  type t = tframe_ty * int

  let equal (i : t) (j : t) = i = j

  let hash (i : t) = Hashtbl.hash i
end

module DSMap = Hashtbl.Make (DSKey)
