module F = Float

exception Error of string

let error s = raise (Error s)

(* misc util functions *)

let fold_for_range_stop_early (f : int -> 'a -> 'a) (low : int) (hi : int)
    (init : 'a) (early_stop : 'a) : int * 'a =
  let rec iter_for_range' (f : int -> 'a -> 'a) (i : int) (agg : 'a) =
    if i > hi || agg = early_stop then (i - 1, agg)
    else iter_for_range' f (i + 1) (f i agg)
  in
  iter_for_range' f low init

(* inclusive on low and hi *)
let fold_for_range (f : int -> 'a -> 'a) (low : int) (hi : int) (init : 'a) : 'a
    =
  let rec iter_for_range' (f : int -> 'a -> 'a) (i : int) (agg : 'a) =
    if i > hi then agg else iter_for_range' f (i + 1) (f i agg)
  in
  iter_for_range' f low init

let iter_for_range (f : int -> unit) (low : int) (hi : int) : unit =
  fold_for_range (fun i () -> f i) low hi ()

let map_for_range (f : int -> 'a) (low : int) (hi : int) : 'a list =
  let rec map_w_fold (i : int) (agg : 'a list) : 'a list = f i :: agg in
  List.rev (fold_for_range map_w_fold low hi [])

let list_of_range = map_for_range (fun i -> i)

let create_reg_pairs (prod_bound : int) (mem_bound : int option) =
  let create_reg_pairs_fixed_n' (n : int) (m : int) (agg : (int * int) list) =
    (n, m) :: agg
    (* if n = 1 && m = 1 then agg else (n, m) :: agg *)
  in
  let create_reg_pairs (n : int) (agg : (int * int) list) =
    fold_for_range (create_reg_pairs_fixed_n' n) n (prod_bound / n) agg
  in
  let lo, hi =
    match mem_bound with
    | Some n ->
        (n, n)
    | None ->
        (1, int_of_float (sqrt (float_of_int prod_bound)))
  in
  fold_for_range create_reg_pairs lo hi []

let list_map (f : 'a -> 'b) (la : 'a list) : 'b list =
  let rec list_map' la lres =
    match la with
    | hda :: tla ->
        list_map' tla (f hda :: lres)
    | [] ->
        List.rev lres
  in
  list_map' la []

let list_map2 (f : 'a -> 'b -> 'c) (la : 'a list) (lb : 'b list) : 'c list =
  let rec list_map2' la lb lres =
    match (la, lb) with
    | hda :: tla, hdb :: tlb ->
        list_map2' tla tlb (f hda hdb :: lres)
    | [], [] ->
        List.rev lres
    | _, _ ->
        raise (Error "[Bug] Invalid_argument in list_map_2")
  in
  list_map2' la lb []

let list_map_3 (f : 'a -> 'b -> 'c -> 'd) (la : 'a list) (lb : 'b list)
    (lc : 'c list) : 'd list =
  let rec list_map_3' la lb lc lres =
    match (la, lb, lc) with
    | hda :: tla, hdb :: tlb, hdc :: tlc ->
        list_map_3' tla tlb tlc (f hda hdb hdc :: lres)
    | [], [], [] ->
        List.rev lres
    | _, _, _ ->
        raise (Error "[Bug] Invalid_argument in list_map_3")
  in
  list_map_3' la lb lc []

let list_map_4 (f : 'a -> 'b -> 'c -> 'd -> 'e) (la : 'a list) (lb : 'b list)
    (lc : 'c list) (ld : 'd list) : 'e list =
  let rec list_map_4' la lb lc ld lres =
    match (la, lb, lc, ld) with
    | hda :: tla, hdb :: tlb, hdc :: tlc, hdd :: tld ->
        list_map_4' tla tlb tlc tld (f hda hdb hdc hdd :: lres)
    | [], [], [], [] ->
        List.rev lres
    | _, _, _, _ ->
        raise (Error "[Bug] Invalid_argument in list_map_4")
  in
  list_map_4' la lb lc ld []

let list_flatten (lla : 'a list list) : 'a list =
  let rec list_flatten' lla lres =
    match lla with
    | [] ->
        List.rev lres
    | la :: tla ->
        list_flatten' tla (List.rev_append la lres)
  in
  list_flatten' lla []

let list_uniq (l : 'a list) =
  List.fold_right (fun x agg -> if List.mem x agg then agg else x :: agg) l []

let list_repeat (size : int) (x : 'a) : 'a list =
  map_for_range (fun _ -> x) 1 size

let cross_prod (ll : 'a list list) =
  let app_to_every_elem_in_list (agg : 'a list list) (elem : 'a) : 'a list list
      =
    list_map (List.cons elem) agg
  in
  let cross_every_list (l : 'a list) (agg : 'a list list) : 'a list list =
    list_map (fun elem -> app_to_every_elem_in_list agg elem) l |> list_flatten
  in
  List.fold_right cross_every_list ll [[]]

let cross_2_lists (la : 'a list) (lb : 'b list) : ('a * 'b) list =
  let cross_list (va : 'a) = list_map (fun vb -> (va, vb)) lb in
  list_map cross_list la |> list_flatten

let split_after_nth (l : 'a list) (index : int) : 'a list * 'a list =
  let rec split_after_nth' l index' fst_l =
    match (l, index') with
    | hd :: tl, 0 ->
        (hd :: fst_l, tl)
    | hd :: tl, _ ->
        split_after_nth' tl (index' - 1) (hd :: fst_l)
    | [], _ ->
        raise (Failure "[split_after_nth] index out of bound.")
  in
  if index = -1 then ([], l)
  else if index < 0 then
    raise (Invalid_argument "[split_after_nth] invalid negative index.")
  else
    let fst_l, snd_l = split_after_nth' l index [] in
    (List.rev fst_l, snd_l)

let slice_num (tot : float) (num_slices : int) : int list =
  let slice_len = tot /. F.of_int num_slices in
  map_for_range
    (fun i ->
      F.to_int (F.round (slice_len *. F.of_int i))
      - F.to_int (F.round (slice_len *. F.of_int (i - 1))) )
    1 num_slices

let slice_num_acc (tot : float) (num_slices : int) : int list =
  let slice_len = tot /. F.of_int num_slices in
  map_for_range
    (fun i -> F.to_int (F.round (slice_len *. F.of_int i)))
    1 num_slices

(* (s, e] *)
(* let range s e = List.init (e - s) (fun x -> s + x) *)

(* Take a list of lists of objects of the form
      [[a1; a2; ... aj]; [b1; b2; ... bk]; ... [c1; c2; ... List]]
    Return a list of all possible combinations of the form
      [[a1; b1; ... c1]; [a1; b1; ... c2]; [a1; b1; ... ck]; ... [a1; b2; ... c1] ... [aj; bk; ... List]] *)
let rec all_combinations (stss : 'a list list) : 'a list list =
  match stss with
  | [] ->
      []
  (* all combinations of a list is a list of singletons *)
  | [sts] ->
      List.map (fun st -> [st]) sts
  (* all combinations of a singleton list with subsequent lists -->
       prepend the singleton to all lists. *)
  | [st] :: stss ->
      let combos = all_combinations stss in
      List.map (fun (combo : 'a list) -> st :: combo) combos
  (* all combinations with every element of first list, separately, then flatten. *)
  | sts :: stss ->
      List.map (fun st -> all_combinations ([st] :: stss)) sts |> List.flatten

let sum xs = List.fold_left ( + ) 0 xs

(* let cons_uniq xs x = if List.mem x xs then xs else x :: xs

   let unique_list_of xs = List.rev (List.fold_left cons_uniq [] xs) *)

module Seq = Core.Sequence

let seq_cons_unique eq xs x =
  let found = Seq.mem ~equal:eq xs x in
  if found then xs else Seq.append xs (Seq.singleton x)

let unique_seq_of eq xs = Seq.fold xs ~init:Seq.empty ~f:(seq_cons_unique eq)

let list_has_dup xs = xs |> list_uniq |> List.length <> (xs |> List.length)

let list_remove xs x = List.filter (fun x_c -> x_c <> x) xs

let remove x xs = list_remove xs x

(* replace the binding in assoc for k with (k, v). If there is
   no binding, append (k, v) to the end. *)
let rec replace_or_app (k, v) assoc =
  match assoc with
  | [] ->
      [(k, v)]
  | (hd_k, hd_v) :: tl -> (
    match String.equal hd_k k with
    | true ->
        (k, v) :: tl
    | false ->
        (hd_k, hd_v) :: replace_or_app (k, v) tl )

let get_from_fields (k : 'a) (assoc : ('a * 'b) list) : 'b option =
  let key_eq (k', v') = if k = k' then true else false in
  let results = List.filter key_eq assoc in
  if List.length results = 0 then None else Some (snd (List.hd results))

(* do lists l1 and l2 intersect? *)
let list_intersect l1 l2 =
  List.fold_left
    (fun acc x -> if List.exists (fun y -> y = x) l1 then true else acc)
    false l2

(* l1 - l2 *)
let list_sub l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1

let list_eq l1 l2 =
  match (list_sub l1 l2, list_sub l2 l1) with [], [] -> true | _ -> false

let list_contains l1 ele = List.exists (fun e -> e = ele) l1

(* do l1 and l2 contain the same elements? *)
let test_set_eq l1 l2 =
  match List.length l1 = List.length l2 with
  | false ->
      false
  | true ->
      let fold_f is_eq l1_entry = is_eq && List.mem l1_entry l2 in
      List.fold_left fold_f true l1

let pair_fold ts pair_acc s = pair_acc @ List.map (fun t -> (s, t)) ts

let get_all_pairs ss ts = List.fold_left (pair_fold ts) [] ss

let rec remove_unordered_pair_dups pairs =
  match pairs with
  | [] ->
      []
  | [x] ->
      [x]
  | (a, b) :: pairs -> (
    match List.mem (a, b) pairs || List.mem (b, a) pairs with
    | true ->
        remove_unordered_pair_dups pairs
    | false ->
        (a, b) :: remove_unordered_pair_dups pairs )

let get_unique_unordered_pairs ss ts =
  get_all_pairs ss ts |> remove_unordered_pair_dups

let rec find_first_dup l =
  match l with
  | [] ->
      None
  | hd :: tl -> (
    match List.exists (( = ) hd) tl with
    | true ->
        Some hd
    | false ->
        find_first_dup tl )

let z_pow2 = Z.shift_left Z.one

let int_pow2 = Int.shift_left 1

let int_log2 n = Z.log2 (Z.of_int n)

let int_log2up n = Z.log2up (Z.of_int n)

let int_cdiv n d = (n + d - 1) / d

let check_num_items (l : 'a list) (num_items : int) (err_msg : string) : unit =
  if List.length l <> num_items then raise (Error err_msg) else ()

let check_num_args (location : string) (args : 'a list) (num_args : int)
    (position : string) : unit =
  check_num_items args num_args
    ( "[" ^ location ^ "] Expecting exactly " ^ string_of_int num_args
    ^ " argument(s) in " ^ position ^ "." )
