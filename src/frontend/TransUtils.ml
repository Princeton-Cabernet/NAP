open SetIR
open P4IR
open SetUtils
open MiscUtils
open Collections
open DataStructUtils
include Petr4.Prunefunc
module P4 = Petr4.P4light
module Cat = CatIR

let check_num_args_tt = check_num_args "TransUtils"

(*************************************************************************
    Cat functions for cleaner synthesis
  *************************************************************************)

let gen_catpred : Cat.e -> Cat.exp = Cat.exp

let gen_catexpr : Cat.e -> Cat.exp = Cat.exp

(* let gen_catstmt : Cat.s -> Cat.statement = Cat.statement *)

(* let gen_catagg (pre_a : Cat.coq_AggregatePreT) : Cat.coq_Aggregate =
   MkAggregate (pre_a, None, Span.dummy) *)

let z_to_bigint (n : Z.t) : Bigint.t = Bigint.of_int (Z.to_int n)

let size_to_bigint (size : Cat.size) : Bigint.t =
  match size with
  | IConst w ->
      Bigint.of_int w
  | _ ->
      raise (Error "[TransUtils] Unexpected size.")

let opt_size_to_z (size : Cat.size option) : Z.t option =
  match size with
  | Some (IConst w) ->
      Some (Z.of_int w)
  | None ->
      None
  | _ ->
      raise (Error "[TransUtils] Unexpected size.")

let opt_z_to_size (width : Z.t option) : Cat.size option =
  match width with Some w -> Some (IConst (Z.to_int w)) | None -> None

let to_p4int (value : Z.t) (width_opt : Z.t option) : Petr4.P4int.t =
  let new_w =
    match width_opt with None -> None | Some w -> Some (z_to_bigint w, false)
  in
  {tags= noinfo; value= z_to_bigint value; width_signed= new_w}

let to_p4expint (value : Z.t) (width_opt : Z.t option) : P4.coq_Expression =
  gen_p4expr (ExpInt (to_p4int value width_opt))

let gen_catint (v : int) (w : int) : Z.t * Z.t option =
  (Z.of_int v, Some (Z.of_int w))

let gen_catexpint (v : int) (w : int) : Cat.exp =
  Cat.eint (Z.of_int v) (Some (IConst w))

let gen_catexpint_z (v : Z.t) (w : int) : Cat.exp = Cat.eint v (Some (IConst w))

let to_p4str_p p s : Petr4.P4string.t = {tags= noinfo; str= p ^ s}

let gen_p4name_p p s : Petr4.P4name.t = BareName (to_p4str_p p s)

let gen_catname ?(init : Cid.t option = None) (ss : string list) : Cid.t =
  match (init, ss) with
  | None, [] ->
      raise
        (Invalid_argument "[TransUtils] gen_catexpname: empty argument list.")
  | None, ss ->
      Cid.create ss
  | Some init, [] ->
      init
  | Some init, ss ->
      Cid.concat init (Cid.create ss)

let gen_catexpname ?(init : Cid.t option = None) (ss : string list) : Cat.exp =
  gen_catexpr (EVar (gen_catname ~init ss))

let str_to_expr s : P4.coq_Expression = gen_p4expname [s]

let str_p_to_expr p s : P4.coq_Expression = gen_p4expname [p ^ s]

let cat_match_dc = MMatch PWild

let cat_act_dft (num_keys : int) =
  MkCatEntry (list_repeat num_keys cat_match_dc, "NoAction", [])

let gen_catmeta (ss : string list) : Cid.t =
  gen_catname ~init:(Some (Cid.create ["_p"; "meta"])) ss

let gen_catexpmeta (ss : string list) : Cat.exp =
  gen_catexpr (EVar (gen_catmeta ss))

(*************************************************************************
    Cat -> P4 translation
  *************************************************************************)

(* Assumptions:
    1. IdVar should have been all resolved into p.meta...., the IdVar case is here
        only for the simplicity of creating ExpExpressionMember.
    2. Only three possible cases after p/h
    3. Only 2 indexes in IdState
*)
let trans_ident (cid : Cid.t) : P4.coq_Expression =
  let cid_names = Cid.names cid |> List.rev in
  let rec trans_ident' names =
    let pre_expr : P4.coq_ExpressionPreT =
      match names with
      | ["meta"; "_p"] ->
          ExpName (gen_p4name "ig_md", noloc)
      | ["ig_intr_md"; "_p"] ->
          ExpName (gen_p4name "ig_intr_md", noloc)
      | ["ig_intr_dprsr_md"; "_p"] ->
          ExpName (gen_p4name "ig_intr_dprsr_md", noloc)
      | ["ig_intr_tm_md"; "_p"] ->
          ExpName (gen_p4name "ig_intr_tm_md", noloc)
      | ["hdr"; "_p"] ->
          ExpName (gen_p4name "hdr", noloc)
      | ["_p"] ->
          raise
            (Error "[TransUtils] Unexpected field after the packet variable.")
      (* | ["_s"; index] ->
         let field =
           if index = "0" then "lo"
           else if index = "1" then "hi"
           else raise (Error "[Bug] Unexpected state variable.")
         in
              ExpExpressionMember
                ( gen_p4expr (ExpName (gen_p4name "ig_intr_md", noloc))
                , to_p4str field )
          | ["_s"] ->
              raise (Error "[TransUtils] Unexpected field after the state variable.") *)
      | [s] ->
          ExpName (gen_p4name s, noloc)
      | name :: names' ->
          ExpExpressionMember (trans_ident' names', to_p4str name)
      | [] ->
          raise (Error "[TransUtils] Unexpected empty ID.")
      (* | IdDontCare ->
          raise (Error "[Bug] IdDontCare should have been resolved.") *)
    in
    gen_p4expr pre_expr
  in
  trans_ident' cid_names

let trans_type (typ : Cat.ty) : P4.coq_P4Type =
  match typ.raw_ty with
  | TBool ->
      TypBool
  (* | TypInt None ->
      TypInteger *)
  | TInt size ->
      TypBit (size_to_bigint size)
  | _ ->
      raise (Error "[Bug] Only TBool and TInt can appear in explicit types.")

(* Assumptions:
    1. ExpPercent should have been resolved and expanded.
*)
let rec trans_expr (e : Cat.exp) : P4.coq_Expression =
  match e.e with
  | EVal {v= VBool b} ->
      gen_p4expr (ExpBool b)
  | EVal {v= VInt n} ->
      to_p4expint n.value (Some n.size)
  | EVal _ ->
      raise (Error "[TransUtils] Unexpected EVal.")
  | EInt (value, size_opt) ->
      to_p4expint value (opt_size_to_z size_opt)
  | EVar cid ->
      trans_ident cid
  | EOp (op, args) ->
      trans_op op args
  | ECall _ ->
      raise (Error "[TransUtils] ECall expression should have been resolved.")
  | ERecord _ ->
      raise (Error "[TransUtils] ERecord expression should have been resolved.")
  | EWith _ ->
      raise (Error "[TransUtils] EWith expression should have been resolved.")
  | ETernary _ ->
      raise (Error "[TransUtils] ETernary expression should have been resolved.")
  | _ ->
      raise (Error "[TransUtils] Unexpected expression.")

(* | ExpPercent _ ->
    raise (Error "[Bug] ExpPercent should have been resolved.") *)

and trans_op (op : Cat.op) (args : Cat.exp list) : P4.coq_Expression =
  match op with
  | TGet _ | PatExact | PatMask ->
      raise (Error "[TransUtils] Unexpected operator.")
  | Not | BitNot | Neg | Cast _ | Slice _ ->
      trans_unaryop op args
  | _ ->
      trans_binaryop op args

and trans_unaryop (op : Cat.op) (args : Cat.exp list) : P4.coq_Expression =
  check_num_args_tt args 1 "unary operation" ;
  let arg = List.hd args |> trans_expr in
  let pre_e : P4.coq_ExpressionPreT =
    match op with
    | Not ->
        ExpUnaryOp (Not, arg)
    | BitNot ->
        ExpUnaryOp (BitNot, arg)
    | Neg ->
        ExpUnaryOp (UMinus, arg)
    | Cast size ->
        ExpCast (trans_type (Cat.ty (TInt size)), arg)
    | Slice (hi, lo) ->
        ExpBitStringAccess (arg, size_to_bigint hi, size_to_bigint lo)
    | _ ->
        raise (Error "[TransUtils] Not unary operator.")
  in
  gen_p4expr pre_e

and trans_binaryop (op : Cat.op) (args : Cat.exp list) : P4.coq_Expression =
  check_num_args_tt args 2 "binary operation" ;
  let larg = List.hd args |> trans_expr in
  let rarg = List.nth args 1 |> trans_expr in
  let pre_e : P4.coq_ExpressionPreT =
    match op with
    | And ->
        ExpBinaryOp (And, larg, rarg)
    | Or ->
        ExpBinaryOp (Or, larg, rarg)
    | Eq ->
        ExpBinaryOp (Eq, larg, rarg)
    | Neq ->
        ExpBinaryOp (NotEq, larg, rarg)
    | Less ->
        ExpBinaryOp (Lt, larg, rarg)
    | More ->
        ExpBinaryOp (Gt, larg, rarg)
    | Leq ->
        ExpBinaryOp (Le, larg, rarg)
    | Geq ->
        ExpBinaryOp (Ge, larg, rarg)
    | Plus ->
        ExpBinaryOp (Plus, larg, rarg)
    | Sub ->
        ExpBinaryOp (Minus, larg, rarg)
    | SatPlus ->
        ExpBinaryOp (PlusSat, larg, rarg)
    | SatSub ->
        ExpBinaryOp (MinusSat, larg, rarg)
    | Conc ->
        ExpBinaryOp (PlusPlus, larg, rarg)
    | BitAnd ->
        ExpBinaryOp (BitAnd, larg, rarg)
    | BitOr ->
        ExpBinaryOp (BitOr, larg, rarg)
    | BitXor ->
        ExpBinaryOp (BitXor, larg, rarg)
    | LShift ->
        ExpBinaryOp (Shl, larg, rarg)
    | RShift ->
        ExpBinaryOp (Shr, larg, rarg)
    | _ ->
        raise (Error "[TransUtils] Not unary operator.")
  in
  gen_p4expr pre_e

(* Assumptions:
    1. Queries inside match statements should have been resolved
       by either merging the match statements into the enum for p and h,
       or using an intermediate meta variable (this case is fine since
       it is clear the meta var is only in enum but not feilds-equality.
       However, allowing using meta in queries generally needs type checker to do
       extra checks)
       (on h: depending on the semantics of if(p...) then (query_of_p))
    2. Match inside match statements should have been resolved.
    3. SEmpty should have been fully removed.
    4. the SConditional case is here only for the simplicity of creating body in action.
*)
let trans_prestmt (s : Cat.dag_stmt) : P4.coq_StatementPreT =
  match s with
  | DSNoop ->
      raise (Error "[Bug] DSNoop statements should have been removed.")
  | DSUnit _ ->
      raise (Error "[Bug] DSUnit statements should have been resolved.")
  | DSLocal (cid, _, exp) | DSAssign (cid, exp) ->
      StatAssignment (trans_ident cid, trans_expr exp)
  | DSMatch _ ->
      raise (Error "[Bug] DSMatch statements should have been resolved.")
  | DSDataStruct _ ->
      raise (Error "[Bug] DSDataStruct statements should have been resolved.")

let trans_stmt (s : Cat.dag_stmt) : P4.coq_Statement =
  gen_p4stmt (trans_prestmt s)

let trans_stmts (ss : Cat.dag_stmt list) : P4.coq_Block =
  List.map trans_stmt ss |> stmt_list_to_block

let trans_pred (pred : predicate) : P4.coq_Expression =
  match pred with
  | PredComp (op, larg, rarg) ->
      trans_expr (Cat.exp (EOp (compop_to_op op, [larg; rarg])))
  | PredNot _ | PredAnd _ | PredOr _ ->
      raise (Error "[Bug] Only PredComp should be tranlsated.")

let resolve_pbit (bits : int list) : Z.t * Z.t * Z.t =
  let list_replace oldv newv l =
    List.map (fun item -> if item = oldv then newv else item) l
  in
  let value = list_replace (-1) 0 bits in
  let mask = list_replace 0 1 bits |> list_replace (-1) 0 in
  let bits_to_z (bits : int list) =
    List.fold_left
      (fun (pos, agg) bit ->
        (pos - 1, if bit = 1 then Z.( + ) (z_pow2 pos) agg else agg) )
      (List.length bits - 1, Z.zero)
      bits
    |> snd
  in
  (bits_to_z value, bits_to_z mask, Z.of_int (List.length bits))

let trans_pat (m : Cat.pat) : P4.coq_Match =
  let pre_m_p4 : P4.coq_MatchPreT =
    match m with
    | PWild ->
        MatchDontCare
    | PNum (value, size_opt) ->
        MatchCast (notype, to_p4expint value (opt_size_to_z size_opt))
    | PRange ((lo_value, lo_size_opt), (hi_value, hi_size_opt)) ->
        MatchRange
          ( to_p4expint lo_value (opt_size_to_z lo_size_opt)
          , to_p4expint hi_value (opt_size_to_z hi_size_opt) )
    | PBit bits ->
        let value, mask, width = resolve_pbit bits in
        MatchMask (to_p4expint value (Some width), to_p4expint mask (Some width))
    | PVar _ ->
        raise (Error "[TransUtils] Unexpected PVar pattern.")
  in
  MkMatch (noinfo, pre_m_p4, notype)

type action_name_map = string StmtsMap.t

let gen_p4actref (args : Cat.exp list) (s : string) : P4.coq_TableActionRef =
  let p4_args = List.map (fun arg -> Some (trans_expr arg)) args in
  MkTableActionRef (noinfo, MkTablePreActionRef (gen_p4name s, p4_args), notype)

let trans_match_entry (placed_act_names : string list) (entry : cat_entry) :
    P4.coq_TableEntry * bool =
  let (MkCatEntry (matches, action_name, args)) = entry in
  let unwrap_match (m : cat_match) : P4.coq_Match =
    match m with
    | MMatch pat ->
        trans_pat pat
    | MIdent cid ->
        gen_p4match (MatchCast (notype, trans_expr (gen_catexpr (EVar cid))))
    | MRange (id1, id2) ->
        gen_p4match
          (MatchRange
             ( trans_expr (gen_catexpr (EVar id1))
             , trans_expr (gen_catexpr (EVar id2)) ) )
  in
  let matches_p4 = List.map unwrap_match matches in
  (* NoAction not in the list of action declarations *)
  if List.mem action_name placed_act_names then
    (MkTableEntry (noinfo, matches_p4, gen_p4actref args action_name), false)
  else (MkTableEntry (noinfo, matches_p4, p4actref_noaction), true)

(* Assumptions:
    1. default action is added in the match entries if not exsiting
    2. To guarantee this, enum smatch must have the default action to cover
       the full key space.
    3. SMatch must have at least 1 action:
        if it is 1, it is the default action, and const entries is set to {}.
*)
let trans_table ?(placed_act_names : string list = []) (table : cat_table) :
    P4.coq_Declaration =
  let (MkCatTable (table_name, ks, mks, entries)) = table in
  (* It is NOT fine to include "NoAction" so that it can generate qualified name. *)
  let placed_act_names =
    if placed_act_names = [] then
      List.map
        (fun e ->
          let (MkCatEntry (_, name, _)) = e in
          if name = "NoAction" then [] else [name] )
        entries
      |> List.flatten |> list_uniq
    else placed_act_names
  in
  let const_entries, default_action_ref, table_actions =
    if List.length entries = 0 then
      raise
        (Error "[Bug] The number of entries in SMatch must be greater than 0.")
    else
      let const_entries, use_noaction_list =
        List.split (List.map (trans_match_entry placed_act_names) entries)
      in
      let use_no_action = List.fold_left ( || ) false use_noaction_list in
      let placed_act_refs = List.map gen_p4actref_na placed_act_names in
      let table_actions =
        if use_no_action then placed_act_refs @ [p4actref_noaction]
        else placed_act_refs
      in
      let (MkTableEntry (_, _, default_action_ref)) =
        List.hd (List.rev const_entries)
      in
      (* For table where there is only one action entry, it must be the default action. *)
      if List.length entries = 1 then ([], default_action_ref, table_actions)
      else (const_entries, default_action_ref, table_actions)
  in
  let table_name = to_p4str table_name in
  let table_keys =
    List.map2
      (fun e mk : P4.coq_TableKey ->
        MkTableKey (noinfo, trans_expr e, to_p4str mk) )
      ks mks
  in
  let table_size = List.length entries in
  DeclTable
    ( noinfo
    , table_name
    , table_keys
    , table_actions
    , Some const_entries
    , Some default_action_ref
    , Some (Bigint.of_int table_size)
    , [] )

let trans_stmt_match (table : cat_table) (placed_actions : cat_action list) :
    prog_tuple =
  let (MkCatTable (table_name, _, _, _)) = table in
  let trans_action (action : cat_action) : P4.coq_Declaration =
    let (MkCatAction (action_name, typ_vars, action_body)) = action in
    let params =
      List.map
        (fun (typ, var) -> gen_p4param Directionless (trans_type typ) var)
        typ_vars
    in
    let action_block = trans_stmts action_body in
    (* No data_param in CatQL right now *)
    DeclAction (noinfo, to_p4str action_name, [], params, action_block)
  in
  let action_decls = List.map trans_action placed_actions in
  let placed_act_names =
    List.map
      (fun action ->
        let (MkCatAction (action_name, _, _)) = action in
        action_name )
      placed_actions
  in
  assert (List.length placed_act_names > 0) ;
  ( []
  , []
  , []
  , action_decls @ [trans_table ~placed_act_names table]
  , [gen_p4tbl_call table_name] )

(*
Omitted for now:
1. cast OR add 0's
2. max bit length
3. typ_env
*)
(* let get_idents_bit_length (ids1 : Cid.t list) (ids2 : Cid.t list) :
     int * P4.coq_Expression * Cat.exp * P4.coq_Expression * Cat.exp =
   let rec concat_idents ids : int * P4.coq_Expression * Cat.exp =
     match ids with
     | [] ->
         (1, gen_p4expint 0 1, gen_catexpint 0 1)
     | [id] ->
         (32, trans_ident id, gen_catexpr (EVar id))
     | id :: tl ->
         let width, tl_p4, tl_cat = concat_idents tl in
         ( 32 + width
         , gen_p4expr (ExpBinaryOp (PlusPlus, trans_ident id, tl_p4))
         , gen_catexpr (EOp (Cat.Conc, [gen_catexpr (EVar id); tl_cat])) )
   in
   let width1, p4expr1, catexpr1 = concat_idents ids1 in
   let width2, p4expr2, catexpr2 = concat_idents ids2 in
   (max width1 width2, p4expr1, catexpr1, p4expr2, catexpr2) *)

(*
Assumptions:
  1. the total length of key after concatenation does not exceed the maximum 
     possible for hashing and PHV.
*)
let concat_keys (keys : Cat.e list) : P4.coq_Expression * Cat.exp =
  let keys = List.map gen_catexpr keys in
  let rec concat_keys' (keys : Cat.exp list) : P4.coq_Expression * Cat.exp =
    match keys with
    | [] ->
        (gen_p4expint 0 1, gen_catexpint 0 1)
    | [key] ->
        (trans_expr key, key)
    | key :: tl ->
        let tl_p4, tl_cat = concat_keys' tl in
        ( gen_p4expr (ExpBinaryOp (PlusPlus, trans_expr key, tl_p4))
        , gen_catexpr (EOp (Cat.Conc, [key; tl_cat])) )
  in
  concat_keys' keys

let gen_p4hashes (crc_num_bit : int) (names : string list) =
  let gen_p4hash name ((coeff, reversed, msb, extended, init, xor), salt_opt) :
      P4.coq_Declaration * (int * int) option * string =
    ( DeclInstantiation
        ( noinfo
        , TypSpecializedType
            ( TypTypeName (to_p4str "CRCPolynomial")
            , [TypBit (Bigint.of_int crc_num_bit)] )
        , [ gen_p4expint coeff crc_num_bit
          ; gen_p4expr (ExpBool reversed)
          ; gen_p4expr (ExpBool msb)
          ; gen_p4expr (ExpBool extended)
          ; gen_p4expint init crc_num_bit
          ; gen_p4expint xor crc_num_bit ]
        , to_p4str name
        , [] )
    , salt_opt
    , name )
  in
  let poly_salt_list = gen_crc_polys crc_num_bit (List.length names) in
  List.map2 gen_p4hash names poly_salt_list
