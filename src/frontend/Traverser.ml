open MiscUtils

module type G = sig
  type t

  module V : Graph.Sig.COMPARABLE

  module E : Graph.Sig.EDGE with type vertex = V.t and type label = int

  val nb_vertex : t -> int

  val succ_e : t -> V.t -> E.t list

  val iter_edges_e : (E.t -> unit) -> t -> unit
end

module Make (G : G) = struct
  module H = Hashtbl.Make (G.V)

  let fold (f : G.V.t -> 'a -> 'a) (h : G.V.t -> G.V.t -> 'b -> unit)
      (g : 'a -> bool) (dag : G.t) (root : G.V.t) (acc : 'a) =
    let n = G.nb_vertex dag in
    let edge_0 = H.create n in
    let edge_12 = H.create n in
    let degree_0 = H.create n in
    (* in-degree of 0-valued edges *)
    (* find: default to 0 *)
    let degree_12 = H.create n in
    (* in-degree of 1-valued edges *)
    (* find: default to 0 *)
    let upd_edge_degree (em : G.E.t list H.t) (dm : int H.t) (e : G.E.t) =
      (let src_node = G.E.src e in
       match H.find_opt em src_node with
       | Some e_list ->
           H.replace em src_node (e :: e_list)
       | None ->
           H.replace em src_node [e] ) ;
      let dst_node = G.E.dst e in
      match H.find_opt dm dst_node with
      | Some deg ->
          H.replace dm dst_node (deg + 1)
      | None ->
          H.replace dm dst_node 1
    in
    let add_degree (e : G.E.t) =
      match G.E.label e with
      | 0 ->
          upd_edge_degree edge_0 degree_0 e
      | 1 | 2 ->
          upd_edge_degree edge_12 degree_12 e
      | _ ->
          raise (Error "[Bug] Unexpected values in the graph edge label.")
    in
    G.iter_edges_e add_degree dag ;
    (* standard topological sort on a DAG *)
    let todo_0 = ref (Queue.create ()) in
    let todo_12 = ref (Queue.create ()) in
    let rec walk acc =
      if Queue.is_empty !todo_0 && Queue.is_empty !todo_12 then acc
      else (
        if Queue.is_empty !todo_0 then (
          todo_0 := !todo_12 ;
          todo_12 := Queue.create () ) ;
        let n = Queue.pop !todo_0 in
        let acc = f n acc in
        match g acc with
        | true ->
            acc
        | _ ->
            let upd_query_degree (dm_upd : int H.t) (dm_query : int H.t)
                (dst_node : G.V.t) (queue : H.key Queue.t ref) =
              let d_u =
                match H.find_opt dm_upd dst_node with
                | Some deg ->
                    let new_deg = deg - 1 in
                    H.replace dm_upd dst_node new_deg ;
                    new_deg
                | None ->
                    0
              in
              let d_q =
                match H.find_opt dm_query dst_node with
                | Some deg ->
                    deg
                | None ->
                    0
              in
              if d_u < 0 || d_q < 0 then
                raise (Error "[Bug] Back edge in the graph.")
              else if d_u = 0 && d_q = 0 then Queue.push dst_node !queue
            in
            let add_succ (e : G.E.t) =
              let dst_node = G.E.dst e in
              match G.E.label e with
              | 0 ->
                  h n dst_node 0 ;
                  upd_query_degree degree_0 degree_12 dst_node todo_0
              | 1 ->
                  h n dst_node 1 ;
                  upd_query_degree degree_12 degree_0 dst_node todo_12
              | 2 ->
                  h n dst_node 2 ;
                  upd_query_degree degree_12 degree_0 dst_node todo_12
              | _ ->
                  raise
                    (Error "[Bug] Unexpected values in the graph edge label.")
            in
            (* must consum 0 edges first: 1-edges push nodes to a strictly later stage than 0-edges *)
            ( match (H.find_opt edge_0 n, H.find_opt edge_12 n) with
            | Some e_list_0, Some e_list_12 ->
                List.iter add_succ e_list_0 ;
                List.iter add_succ e_list_12
            | Some e_list_0, None ->
                List.iter add_succ e_list_0
            | None, Some e_list_12 ->
                List.iter add_succ e_list_12
            | None, None ->
                () ) ;
            walk acc )
    in
    Queue.push root !todo_0 ; walk acc

  let iter f h dag root = fold (fun v () -> f v) h (fun () -> false) dag root ()

  let simple_fold f dag root acc =
    fold f (fun _ _ _ -> ()) (fun acc -> false) dag root acc

  let simple_iter f dag root =
    fold (fun v () -> f v) (fun _ _ _ -> ()) (fun () -> false) dag root ()
end