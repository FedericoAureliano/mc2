(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

open Mc2_core

module Loc = Smtlib_utils.V_2_6.Loc
module PA = Smtlib_utils.V_2_6.Ast
module SReg = Service.Registry
module Ty = Mc2_core.Type
module T = Mc2_core.Term
module F = Mc2_propositional.F
module RLE = Mc2_lra.LE
module Stmt = Mc2_core.Statement

(* Amar: adding a "state" that will keep track of the number of variables  *)
(* type state =  { mutable number_terms : int}; *)
(* type adt = ((string * level) * (PA.cstor list)) list
type state_type = {ADT_instances : (adt list)}
let state : state_type = {ADT_instances = []} *)
(*end: Amar section  *)

type 'a or_error = ('a, string) CCResult.t

let pp_loc_opt = Loc.pp_opt

module StrTbl = CCHashtbl.Make(CCString)
(*module SS = Set.Make(PA.ty) (* will use set to keep track of variables*)*)


(* want to keep track of the adt_variables in a hashtable indexed by type*)
module TyTbl = Hashtbl.Make(struct
  type t = PA.ty
  let equal = (=)
  let hash = Hashtbl.hash
end)

(* want to keep track of the adts in a hashtable indexed by their id*)
module IntTbl = Hashtbl.Make(struct
  type t = int
  let equal = (=)
  let hash = Hashtbl.hash
end)

(* Helper function added by Amar *)
let rec print_list = function 
  |[] -> ()
  | e::l -> print_string e ; print_string " " ; print_list l

(* let rec print_stmts = function 
  |[] -> ()
  | e::l -> Stmt.pp e ; print_string " " ; (print_stmts l) *)

module Make(ARG : sig
    val solver : Mc2_core.Solver.t
  end)
= struct
  let solver = ARG.solver
  let reg = Solver.services solver
  let decl = Solver.get_service_exn solver Mc2_uf.k_decl

  module BV = Bound_var

  type term_or_form =
    | T of term
    | F of F.t
    | Rat of RLE.t (* rational linear expression *)

  module Ctx = struct
    type t = {
      tys: (ID.t * Type.t) StrTbl.t;
      adt_tys: (ID.t * Type.t) IntTbl.t; (* we did an int tbl here so we could index them by their id and not their name *)
      terms: ID.t StrTbl.t;
      sel_terms: ID.t StrTbl.t;
      constr_terms: ID.t StrTbl.t;
      def_funs: (PA.typed_var list * PA.term) StrTbl.t; (* defined functions *)
      def_consts: term_or_form StrTbl.t; (* defined constants *)
      def_adts: (PA.cstor list) StrTbl.t; (* defined adts *)
      def_adt_byid: string IntTbl.t; (* same table as def_adts, but now we index by the id of an adt*)
      adt_constructor: (PA.cstor * string) StrTbl.t; (* defined adt constructors: should point to their respective adts *)
      def_adt_vars: (int * PA.ty) StrTbl.t; (* defined all of the variables for ADTS: variable name, constructor: may want to include other information like selector tester, etc *)
      mutable loc: Loc.t option; (* current loc *)
      mutable max_depth: int;
      mutable vars_created: int;
    }

    let t : t = {
      terms=StrTbl.create 64;
      sel_terms=StrTbl.create 64;
      constr_terms = StrTbl.create 64;
      tys=StrTbl.create 64;
      adt_tys=IntTbl.create 64;
      def_funs=StrTbl.create 64;
      def_consts=StrTbl.create 32;
      def_adts = StrTbl.create 64;
      def_adt_byid = IntTbl.create 64;
      adt_constructor = StrTbl.create 64;
      def_adt_vars = StrTbl.create 64;
      loc=None;
      max_depth = 0;
      vars_created = 0;
    }

    let loc t = t.loc
    let set_loc ?loc () = t.loc <- loc

    let add_term_fun_ (s:string) (id:ID.t) : unit =
      StrTbl.replace t.terms s id;
      ()

      (*trying to create a version of add_term_fun_ for selectors.
         TODO: figure out what needs to be different*)
    let add_term_sel_ (s:string) (id:ID.t) : unit =
      print_string (s ^ " added to context as selector \n");
      StrTbl.replace t.sel_terms s id;
      (* Printf.printf "Keys: %s\n" (String.concat " " (StrTbl.keys_list def_selectors )); *)
      ()
    
    let add_term_constr_ (s:string) (id:ID.t) : unit =
      print_string (s ^ " added to context as constructor \n");
      StrTbl.replace t.constr_terms s id;
      ()

    let add_ty_ (s:string) (id:ID.t) (ty:Ty.t) : unit =
      StrTbl.replace t.tys s (id,ty);
      ()

    let add_adt_ty_ (n:int) (id:ID.t) (ty:Ty.t) : unit =
      IntTbl.replace t.adt_tys n (id,ty);
      ()

    let add_def_const s rhs : unit = StrTbl.add t.def_consts s rhs
    let add_def_fun s vars rhs : unit = StrTbl.add t.def_funs s (vars,rhs)
    let add_def_adt name constructors : unit = StrTbl.add t.def_adts name constructors
    let add_def_adt_byid id name : unit = IntTbl.add t.def_adt_byid id name
    let add_adt_constructor name adt constructor : unit = StrTbl.add t.adt_constructor name (constructor, adt)
    let add_adt_vars name adt_type id : unit = StrTbl.add t.def_adt_vars name (id, adt_type) (* adding a new adt variable to the context*)
    let print_adt_vars (): unit = 
      print_list (StrTbl.keys_list t.def_adt_vars)
    let update_max_depth n : unit = 
        t.max_depth <- max t.max_depth n
    let increment_vars_created () : unit = 
      t.vars_created <- t.vars_created + 1

    let check_def_adt name : PA.cstor list option = StrTbl.find_opt t.def_adts name



    let find_ty (s:string) : ty =
      match StrTbl.get t.tys s with
      | Some (_, ty) -> ty
      | _ -> Error.errorf "expected %s to be an atomic type" s

    let in_adt_ty (n:int) =
      match IntTbl.find_opt t.adt_tys n with
      | Some(_, ty) -> true
      | None -> false

    let find_term_fun (s:string) : ID.t option =
      match StrTbl.get t.terms s with
      | Some f -> Some f
      | _ -> None (*Error.errorf "expected %s to be a function symbol" s*)

    let find_term_sel (s:string) : ID.t option =
      match StrTbl.get t.sel_terms s with
      | Some f -> Some f
      | _ -> None

    let find_term_constr (s:string) : ID.t option =
      match StrTbl.get t.constr_terms s with
      | Some f -> Some f
      | _ -> None
  end

  let error_loc () : string = Fmt.sprintf "at %a: " pp_loc_opt (Ctx.loc Ctx.t)
  let errorf_ctx msg =
    Error.errorf ("at %a:@ " ^^ msg) pp_loc_opt (Ctx.loc Ctx.t)

  let ill_typed fmt =
    errorf_ctx ("ill-typed: " ^^ fmt)

  (* parse a type *)
  let conv_ty (t:PA.ty) : Ty.t = match t with
    | PA.Ty_bool -> Ty.bool
    | PA.Ty_real ->
      SReg.find_exn reg Mc2_lra.k_rat
    | PA.Ty_app ("Rat",[]) ->
      ill_typed "cannot handle reals for now"
    | PA.Ty_app ("Int",[]) ->
      ill_typed "cannot handle ints for now"
      (* TODO: A.Ty.int , Ctx.K_ty Ctx.K_other *)
    | PA.Ty_app (f, []) -> Ctx.find_ty f
    | PA.Ty_app (_f, _l) ->
      ill_typed "cannot handle parametric types"
    | PA.Ty_arrow _ ->
      ill_typed "cannot handle arrow types"

  module Subst = struct
    module M = Util.Str_map
    type 'a t = 'a M.t
    let empty = M.empty
    let mem subst v = M.mem v subst
    let add subst v t =
      if mem subst v then (
        Error.errorf "%a already bound" Fmt.string v;
      );
      M.add v t subst
    let find subst v = M.get v subst
  end

  let is_num s =
    let is_digit_or_dot = function '0' .. '9' | '.' -> true | _ -> false in
    if s.[0] = '-'
    then CCString.for_all is_digit_or_dot (String.sub s 1 (String.length s-1))
    else CCString.for_all is_digit_or_dot s

  let mk_ite_id =
    let n = ref 0 in
    fun () -> ID.makef "ite_%d" (CCRef.incr_then_get n)

  let mk_sub_form =
    let n = ref 0 in
    fun () -> ID.makef "sub_form_%d" (CCRef.incr_then_get n)

  let mk_lra_id =
    let n = ref 0 in
    fun () -> ID.makef "lra_%d" (CCRef.incr_then_get n)



  let[@inline] ret_t t = T t
  let[@inline] ret_f f = F f
  let[@inline] ret_rat t = Rat t
  let ret_any t =
    if Term.is_bool t then F (F.atom (Term.Bool.pa t)) else T t

  let pp_tof out = function
    | T t -> Fmt.fprintf out "(@[T %a@])" Term.pp t
    | F f -> Fmt.fprintf out "(@[F %a@])" F.pp f
    | Rat lre -> Fmt.fprintf out "(@[RLE %a@])" RLE.pp_no_paren lre

  let parse_num ~where (s:string) : [`Q of Q.t | `Z of Z.t] =
    let fail() =
      Error.errorf "%sexpected number, got `%s`" (Lazy.force where) s
    in
    begin match Z.of_string s with
      | n -> `Z n
      | exception _ ->
        begin match Q.of_string s with
          | n -> `Q n
          | exception _ ->
            if String.contains s '.' then (
              let p1, p2 = CCString.Split.left_exn ~by:"." s in
              let n1, n2 =
                try Z.of_string p1, Z.of_string p2
                with _ -> fail()
              in
              let factor_10 = Z.pow (Z.of_int 10) (String.length p2) in
              (* [(p1·10^{length p2}+p2) / 10^{length p2}] *)
              let n =
                Q.div
                  (Q.of_bigint (Z.add n2 (Z.mul n1 factor_10)))
                  (Q.of_bigint factor_10)
              in
              `Q n
            ) else fail()
        end
    end

  let side_clauses = ref []

  let mk_const = SReg.find_exn reg Mc2_uf.k_const
  let mk_lra_pred = SReg.find_exn reg Mc2_lra.k_make_pred
  let mk_lra_eq t u = mk_lra_pred Mc2_lra.Eq0 (RLE.diff t u) |> Term.Bool.pa
  let[@inline] mk_eq_ t u = Term.mk_eq t u
  let mk_eq t u = Term.Bool.pa (mk_eq_ t u)
  let mk_neq t u = Term.Bool.na (mk_eq_ t u)

  module LRA_tbl = CCHashtbl.Make(RLE)
  let _lra_names = LRA_tbl.create 16

  (* introduce intermediate variable for LRA sub-expression *)
  let mk_lra_expr (e:RLE.t): term =
    match RLE.as_const e, RLE.as_singleton e with
    | Some n, _ -> SReg.find_exn reg Mc2_lra.k_make_const n
    | None, Some (n,t) when Q.equal n Q.one -> t
    | _ ->
      begin match LRA_tbl.find _lra_names e with
      | t -> t
      | exception Not_found ->
        let id = mk_lra_id() in
        Log.debugf 30
          (fun k->k"(@[smtlib.name_lra@ %a@ :as %a@])" RLE.pp e ID.pp id);
        decl id [] (SReg.find_exn reg Mc2_lra.k_rat);
        let t = mk_const id in
        side_clauses := [mk_lra_eq (RLE.singleton1 t) e] :: !side_clauses;
        LRA_tbl.add _lra_names e t; (* cache *)
        t
      end

  (* adaptative equality *)
  let mk_eq_t_tf (t:term) (u:term_or_form) : F.t = match u with
    | F u -> F.equiv (F.atom (Term.Bool.pa t)) u
    | T u when Term.is_bool u ->
      F.equiv (F.atom (Term.Bool.pa t)) (F.atom (Term.Bool.pa u))
    | T u -> mk_eq t u |> F.atom
    | Rat u -> mk_lra_eq (RLE.singleton1 t) u |> F.atom
  let mk_eq_tf_tf (t:term_or_form) (u:term_or_form) = match t, u with
    | T t, T u when Term.is_bool t ->
      F.equiv (F.atom (Term.Bool.pa t)) (F.atom (Term.Bool.pa u))
    | T t, T u -> mk_eq t u |> F.atom
    | T t, Rat u | Rat u, T t -> mk_lra_eq (RLE.singleton1 t) u |> F.atom
    | Rat t, Rat u -> mk_lra_eq t u |> F.atom
    | F t, F u -> F.equiv t u
    | F t, T u -> F.equiv t (F.atom @@ Term.Bool.pa u)
    | T t, F u -> F.equiv (F.atom @@ Term.Bool.pa t) u
    | _ ->
      Log.debugf 1 (fun k->k "eq %a %a" pp_tof t pp_tof u);
      assert false

  (* convert term *)
  let rec conv_t_or_f_ (subst:term_or_form Subst.t) (t:PA.term) : term_or_form =
    (* polymorphic equality *)
    let mk_app = SReg.find_exn reg Mc2_uf.k_app in
    let mk_const = SReg.find_exn reg Mc2_uf.k_const in
    let conv_const v =
      begin match Subst.find subst v with
        | Some t -> t
        | None when is_num v ->
          (* numeral *)
          begin match parse_num ~where:(lazy (error_loc ())) v with
            | `Q n -> Mc2_lra.LE.const n |> ret_rat
            | `Z n -> Mc2_lra.LE.const (Q.of_bigint n) |> ret_rat
          end
        | _ ->
          (* look for definitions *)
          match StrTbl.find Ctx.t.Ctx.def_consts v with
          | rhs -> rhs
          | exception Not_found ->
            match Ctx.find_term_fun v with
            | Some f -> mk_app f [] |> ret_any
            | None ->
              match Ctx.find_term_sel v with
              | Some f -> mk_app f [] |> ret_any
              | None -> Error.errorf "variable %S not bound" v
        end
    in
    begin match t with
      | PA.Const v -> conv_const v
      | PA.App ("xor", [a;b]) -> F.xor (conv_form subst a) (conv_form subst b) |> ret_f
      | PA.App (f, []) -> conv_const f
      | PA.App (f, l) ->
        (* see if it's a defined function *)
        begin match StrTbl.find Ctx.t.Ctx.def_funs f with
          | (vars,rhs) ->
            (* TODO: also check types *)
            if List.length vars <> List.length l then (
              errorf_ctx "invalid function call to %s" f
            );
            let l = List.map (conv_t_or_f_ subst) l in
            let subst =
              List.fold_left2 (fun s (v,_) t -> Subst.add s v t) Subst.empty vars l
            in
            conv_t_or_f_ subst rhs
          | exception Not_found ->
            begin match Ctx.find_term_fun f  with 
             |Some id -> let l = List.map (conv_term_ subst) l in
                    mk_app id l |> ret_any
             |None ->
                begin match Ctx.find_term_sel f with
                  | Some id -> let l = List.map (conv_term_ subst) l in
                              mk_app id l |> ret_any
                  | None -> Error.errorf "variable %S not bound" f
                end 
            end
        end
      | PA.If (a,b,c) ->
        let a = conv_form subst a in
        let b = conv_t_or_f_ subst b in
        let c = conv_t_or_f_ subst c in
        let ty_b = match b with
          | F _ -> Type.bool
          | T t -> Term.ty t
          | Rat _ -> SReg.find_exn reg Mc2_lra.k_rat
        in
        let placeholder_id = mk_ite_id () in
        Log.debugf 30
          (fun k->k"(@[smtlib.name_term@ %a@ :as %a@])" PA.pp_term t ID.pp placeholder_id);
        decl placeholder_id [] ty_b;
        let placeholder = mk_const placeholder_id in
        (* add [f_a => placeholder=b] and [¬f_a => placeholder=c] *)
        let form =
          F.and_
            [ F.imply a (mk_eq_t_tf placeholder b);
              F.imply (F.not_ a) (mk_eq_t_tf placeholder c);
            ]
        in
        let cs = mk_cnf form in
        side_clauses := List.rev_append cs !side_clauses;
        ret_any placeholder
      | PA.Let (bs,body) ->
        (* convert all bindings in the same surrounding [subst],
           then convert [body] with all bindings active *)
        let subst =
          List.fold_left
            (fun subst' (v,t) -> Subst.add subst' v (conv_t_or_f_ subst t))
            subst bs
        in
        conv_t_or_f_ subst body
      | PA.And l -> F.and_ (List.map (conv_form subst) l) |> ret_f
      | PA.Or l -> F.or_ (List.map (conv_form subst) l) |> ret_f
      | PA.Imply (a,b) ->
        ret_f @@ F.imply (conv_form subst a) (conv_form subst b)
      | PA.Eq (a,b) ->
        let a = conv_t_or_f_ subst a in
        let b = conv_t_or_f_ subst b in
        mk_eq_tf_tf a b |> ret_f
      | PA.Distinct l ->
        (* TODO: more efficient "distinct"? *)
        List.map (conv_term_ subst) l
        |> CCList.diagonal
        |> List.map (fun (t,u) -> mk_neq t u |> F.atom)
        |> F.and_ |> ret_f
      | PA.Not f -> F.not_ (conv_form subst f) |> ret_f
      | PA.True -> ret_f F.true_
      | PA.False -> ret_f F.false_
      | PA.Arith (op, l) ->
        let l = List.map (conv_rat subst) l in
        begin match op, l with
          | PA.Minus, [a] -> RLE.neg a |> ret_rat
          | PA.Leq, [a;b] ->
            let e = RLE.diff a b in
            mk_lra_pred Mc2_lra.Leq0 e |> ret_any
          | PA.Geq, [a;b] ->
            let e = RLE.diff b a in
            mk_lra_pred Mc2_lra.Leq0 e |> ret_any
          | PA.Lt, [a;b] ->
            let e = RLE.diff a b in
            mk_lra_pred Mc2_lra.Lt0 e |> ret_any
          | PA.Gt, [a;b] ->
            let e = RLE.diff b a in
            mk_lra_pred Mc2_lra.Lt0 e |> ret_any
          | (PA.Leq | PA.Lt | PA.Geq | PA.Gt), _ ->
            Error.errorf "ill-formed arith expr:@ %a@ (binary operator)" PA.pp_term t
          | PA.Add, _ ->
            let e = List.fold_left (fun n t -> RLE.add t n) RLE.empty l in
            mk_lra_expr e |> ret_t
          | PA.Minus, a::tail ->
            let e =
              List.fold_left
                (fun n t -> RLE.diff n t)
                a tail
            in
            mk_lra_expr e |> ret_t
          | PA.Mult, _::_::_ ->
            let coeffs, terms =
              CCList.partition_filter_map
                (fun t -> match RLE.as_const t with
                   | None -> `Right t
                   | Some c -> `Left c)
                l
            in
            begin match coeffs, terms with
              | c::c_tail, [] ->
                List.fold_right RLE.mult c_tail (RLE.const c) |> ret_rat
              | _, [t] ->
                List.fold_right RLE.mult coeffs t |> ret_rat
              | _ ->
                Error.errorf "non-linear expr:@ `%a`" PA.pp_term t
            end
          | PA.Div, (first::l) ->
            (* support t/a/b/c where only [t] is a rational *)
            let coeffs =
              List.map
                (fun c -> match RLE.as_const c with
                   | None ->
                     Error.errorf "non-linear expr:@ `%a`" PA.pp_term t
                   | Some c -> Q.inv c)
                l
            in
            List.fold_right RLE.mult coeffs first |> ret_rat
          | (PA.Minus | PA.Div | PA.Mult), ([] | [_]) ->
            Error.errorf "ill-formed arith expr:@ %a@ (binary operator)" PA.pp_term t
        end
      | PA.Attr (t,_) -> conv_t_or_f_ subst t
      | PA.Cast (t, ty_expect) ->
        let t = conv_term_ subst t in
        let ty_expect = conv_ty ty_expect in
        if not (Ty.equal (Term.ty t) ty_expect) then (
          ill_typed "term `%a`@ should have type `%a`" Term.pp t Ty.pp ty_expect
        );
        ret_any t
      | PA.HO_app _ ->
        errorf_ctx "cannot handle HO application"
      | PA.Fun _ -> errorf_ctx "cannot handle lambdas"
      | PA.Match (_lhs, _l) ->
        errorf_ctx "cannot handle match"
      | PA.Is_a _ ->
        errorf_ctx "cannot handle is-a" (* TODO *)
      | PA.Forall _ | PA.Exists _ ->
        errorf_ctx "cannot handle quantifiers" (* TODO *)
    end

  (* expect a term *)
  and conv_term_ subst (t:PA.term) : term =
    match conv_t_or_f_ subst t with
    | T t -> t
    | Rat e -> mk_lra_expr e
    | F {F.view=F.Lit a;_} when Atom.is_pos a -> Atom.term a
    | F ({F.view=F.Lit _;_} as f) ->
      (* name [¬a] *)
      let placeholder_id = mk_sub_form() in
      decl placeholder_id [] Type.bool;
      let placeholder = mk_const placeholder_id in
      Log.debugf 30
        (fun k->k"(@[smtlib.name_atom@ %a@ :as %a@])" F.pp f ID.pp placeholder_id);
      (* add [placeholder <=> ¬a] *)
      let form = F.equiv (F.atom (Term.Bool.na placeholder)) f in
      side_clauses := List.rev_append (mk_cnf form) !side_clauses;
      placeholder
    | F f ->
      (* name the sub-formula and add CNF *)
      let placeholder_id = mk_sub_form() in
      decl placeholder_id [] Type.bool;
      Log.debugf 30
        (fun k->k"(@[smtlib.name_subform@ %a@ :as %a@])" F.pp f ID.pp placeholder_id);
      let placeholder = mk_const placeholder_id in
      (* add [placeholder <=> f] *)
      let form = F.equiv (F.atom (Term.Bool.pa placeholder)) f in
      side_clauses := List.rev_append (mk_cnf form) !side_clauses;
      placeholder

  and mk_cnf (f:F.t) : atom list list =
    let fresh = SReg.find_exn reg Mc2_propositional.k_fresh in
    F.cnf ~fresh f

  (* convert formula *)
  and conv_form subst (t:PA.term): F.t = match conv_t_or_f_ subst t with
    | T t -> F.atom (Term.Bool.pa t)
    | F f -> f
    | Rat _ -> Error.errorf "expected proposition,@ got %a" PA.pp_term t

  (* expect a rational expr *)
  and conv_rat subst (t:PA.term) : RLE.t =
    match conv_t_or_f_ subst t with
    | Rat e -> e
    | T t -> RLE.singleton1 t
    | F _ -> assert false

  let wrap_side_ (f:unit -> 'a) : atom list list * 'a =
    assert (!side_clauses = []);
    let x = f() in
    let side = !side_clauses in
    side_clauses := [];
    side, x

  let conv_term_or_form (t:PA.term) =
    wrap_side_ (fun () -> conv_t_or_f_ Subst.empty t)

  let conv_bool_term (t:PA.term): atom list list =
    let side, cs =
      wrap_side_ (fun () -> conv_form Subst.empty t |> mk_cnf)
    in
    List.rev_append side cs

  let conv_fun_decl f : string * Ty.t list * Ty.t =
    if f.PA.fun_ty_vars <> [] then (
      errorf_ctx "cannot convert polymorphic function@ %a"
        (PA.pp_fun_decl PA.pp_ty) f
    );
    let args = List.map conv_ty f.PA.fun_args in
    let ret = conv_ty f.PA.fun_ret in
    f.PA.fun_name, args, ret

  (* Amar: trying to create a version of conv_fun_decl for datatypes *)
  (* let conv_fun_data f: ((string * level) * PA.Cstor list) list =
    if f.PA.fun_ty_vars <> [] then (
      errorf_ctx "cannot convert polymorphic function@ %a"
        (PA.pp_fun_decl PA.pp_ty) f
    );
    let args = List.map conv_ty f.PA.fun_args in
    let ret = conv_ty f.PA.fun_ret in
    f.PA.fun_name, args, ret *)
    (* end Amar section *)

  let conv_term t = conv_term_ Subst.empty t

  let rec conv_statement (s:PA.statement): Stmt.t list =
    Log.debugf 4 (fun k->k "(@[<1>statement_of_ast@ %a@])" PA.pp_stmt s);
    Ctx.set_loc ?loc:(PA.loc s) ();
    conv_statement_aux s
  
  and conv_statement_aux_sel (stmt:PA.statement) : Stmt.t list =
  begin match PA.view stmt with
    | PA.Stmt_decl fr ->
      Log.debugf 5 (fun k->k ">>> conv stmt decl %a" (PA.pp_fun_decl PA.pp_ty) fr);
      let f, args, ret = conv_fun_decl fr in
      let id = ID.make f in
      decl id args ret;
      Ctx.add_term_sel_ f id;
      [Stmt.Stmt_decl (id, args,ret)]
    | _ -> errorf_ctx "non-selector inputted as selector"
    end

    and conv_statement_aux_constr (stmt:PA.statement) : Stmt.t list =
      begin match PA.view stmt with
        | PA.Stmt_decl fr ->
          Log.debugf 5 (fun k->k ">>> conv stmt decl %a" (PA.pp_fun_decl PA.pp_ty) fr);
          let f, args, ret = conv_fun_decl fr in
          let id = ID.make f in
          decl id args ret;
          Ctx.add_term_constr_ f id;
          begin match fr.PA.fun_ret with
            | PA.Ty_app (f, []) -> 
                  begin match ret with 
                    |Bool -> () (*TODO: throw an erro if it is a bool*)
                    |Ty { id; view; _} -> 
                      (* print_string ("this is the id of " ^ fr.fun_name ^ ": "); print_int id; print_string "\n"; *)
                      if ((Ctx.in_adt_ty id) && (args == [])) then print_string ("added adt variable to context " ^ fr.fun_name ^ "\n"); 
                      if ((Ctx.in_adt_ty id) && (args == [])) then Ctx.add_adt_vars fr.fun_name fr.fun_ret id
                      (* what I need in adt_vars: the constructors <-> selectors <-> testers given in corrspondence. this should probably be added when we define the adt*)
                  end
            |_ ->()
          end;
          print_string ("happens" ^ f ^ "\n");
          Ctx.add_term_fun_ f id;
          [Stmt.Stmt_decl (id, args,ret)]
        | _ -> errorf_ctx "non-constructor inputted as constructor"
      end

    and conv_statement_aux_adt (stmt:PA.statement) : Stmt.t list =
    match PA.view stmt with
    | PA.Stmt_decl_sort (s,n) ->
      if n > 0 then (
        errorf_ctx "cannot handle polymorphic type %s" s (* TODO *)
      );
      let id_thing = ID.make s in
      (* declare type, and save it *)
      SReg.find_exn reg Mc2_unin_sort.k_decl_sort id_thing n;
      let ty = SReg.find_exn reg Mc2_unin_sort.k_make id_thing [] in
      (* print_string ("ADDED TO CONTEXT : " ^ s ^ "\n"); *)
      Ctx.add_ty_ s id_thing ty;
      begin match ty with 
        |Bool -> ()
        |Ty { id; _ } -> (*print_string ("adding adt_ty: " ^ s ^ " and this is the real id(hopefully): "); print_int id; print_string "\n";*)
                         Ctx.add_def_adt_byid id s;
                         Ctx.add_adt_ty_ id id_thing ty; (* Saving the fact that this is an adt type in addition to just a regular type*)

      end;
      (* print_string ("adding adt_ty: " ^ s ^ " and this is the id: "); print_int ((ID.id) id_thing); print_string "\n"; *)
      [Stmt.Stmt_ty_decl (id_thing, n)]

      | _ -> errorf_ctx "non-adt sort inputted as adt"




  and conv_statement_aux (stmt:PA.statement) : Stmt.t list =
    match PA.view stmt with
    | PA.Stmt_set_logic s -> [Stmt.Stmt_set_logic s]
    | PA.Stmt_set_option l -> [Stmt.Stmt_set_option l]
    | PA.Stmt_set_info (a,b) -> [Stmt.Stmt_set_info (a,b)]
    | PA.Stmt_exit -> [Stmt.Stmt_exit]
    | PA.Stmt_decl_sort (s,n) ->
      if n > 0 then (
        errorf_ctx "cannot handle polymorphic type %s" s (* TODO *)
      );
      let id = ID.make s in
      (* declare type, and save it *)
      (* TODO: when handling polymorphic types, will have to kill ctx.types
         and use the function Mc2_unin_sort.k_make directly *)
      SReg.find_exn reg Mc2_unin_sort.k_decl_sort id n;
      let ty = SReg.find_exn reg Mc2_unin_sort.k_make id [] in
      Ctx.add_ty_ s id ty;
      [Stmt.Stmt_ty_decl (id, n)]
    | PA.Stmt_decl fr ->
      (*TODO(Phase 3): This is where variables are defined. So I want to check if it is a constant
                        and if its type is an ADT and if so, then store some information about it.*)
      (* It would be nice for the sake of testing to be able to print out a PA.ty, but I'm not sure how to do that*)
      Log.debugf 5 (fun k->k ">>> conv stmt decl %a" (PA.pp_fun_decl PA.pp_ty) fr);
      let f, args, ret = conv_fun_decl fr in

      (* Bunch of testing stuff*)
      (* print_string ("defining a variable: " ^ f ^ "\n");
      let rec find_type (return: PA.ty) = 
        begin match return with
          | PA.Ty_bool -> print_string "Type: bool \n"
          | PA.Ty_real  -> print_string "Type: real \n"
          | PA.Ty_app (_, _) -> print_string "Type: app \n"
          | PA.Ty_arrow (_, _) -> print_string "Type: arrow \n"
        end
      in
      (* begin match (args, ret) with
        |([arg], _) -> (Ctx.add_adt_vars f arg);
        | _ -> ;
      end *)
      print_string "here are the variables: ";
      print_list fr.PA.fun_ty_vars;
      PA.fpf Format.std_formatter "(@[declare-fun@ %a@])" (PA.pp_par (PA.pp_fun_decl PA.pp_ty)) (fr.PA.fun_ty_vars,fr);
      print_string "\n";

      find_type fr.PA.fun_ret; *)


      (* let rec print_args (l: PA.typed_var list) = 
        begin match l with 
          | (s, t)::body -> print_string s; print_args body
          |[] -> ()
          |_ -> ()
        end
      in
      print_args fr.fun_args; *)


      (* here i am adding the variable to the context kinda, but it is a little weird since I'm not sure if fun_ret is the right type*)
      (* the other issue is that i only want to do this for adts and not regular sorts, but with my current implementation, I do not differentiate between the two*)

      (* phase 3: this doesn't work right now but should check if our sort is in the adt thing and then add vars if so*)

      (* module Unin = Mc2_unin_sort; *)

      (*ISSUE: need this Unin thing to work*)
      begin match fr.PA.fun_ret with
        | PA.Ty_app (f, []) -> 
              begin match ret with 
                |Bool -> () (*TODO: throw an erro if it is a bool*)
                |Ty { id; view; _} -> 
                  (* print_string ("this is the id of " ^ fr.fun_name ^ ": "); print_int id; print_string "\n"; *)
                  if ((Ctx.in_adt_ty id) && (args == [])) then print_string ("added adt variable to context " ^ fr.fun_name ^ "\n"); 
                  if ((Ctx.in_adt_ty id) && (args == [])) then Ctx.add_adt_vars fr.fun_name fr.fun_ret id;
                  (* what I need in adt_vars: the constructors <-> selectors <-> testers given in corrspondence. this should probably be added when we define the adt*)
              end
        |_ ->()
      end;

      (* print_string ("checking if adt_ty: " ^ fr.fun_name ^ "\n"); *)


      (* begin match Ctx.find_adt_ty fr.fun_name with 
        |Some(ty) -> Ctx.add_adt_vars fr.fun_name fr.fun_ret
        |None -> ()
      end *)

      (* begin match (StrTbl.get Ctx.t.adt_tys fr.fun_name) with
        | Some (_, ty) -> Ctx.add_adt_vars fr.fun_name fr.fun_ret;
        | _ -> ();
      end *)


      let id = ID.make f in
      decl id args ret;
      Ctx.add_term_fun_ f id;
      [Stmt.Stmt_decl (id, args,ret)]
    | PA.Stmt_data _l -> 
      (* errorf_ctx "cannot handle datatype in %a" PA.pp_stmt stmt *)
      (* TODO Federico: store data type information for processing later *)
      (* TODO Federico: follow case above for PA.Stmt_decl to add declarations for our blasting *)
      (* Everything between this and the next comment was written by Amar*)
      (* I am not really sure how to find cstor_type in the below function *)
      let rec make_selectors (cstor_name: string) (cstor_type: PA.ty) (cstor_args: (string * PA.ty) list) (m: int) =
        begin match cstor_args with
          |[] -> []
          |(s, t)::body ->
            (* begin match t with
              |PA.Ty_app (v, []) -> print_string ("   selector: " ^ s ^ " of type: " ^ v);
              |_ -> print_string "";
            end; *)
            (* print_string ("   selector: " ^ s ^"(" ^cstor_name ^")"); *)
            List.append (conv_statement_aux_sel({ loc = stmt.loc; 
                                             stmt = (Stmt_decl ({fun_ty_vars = []; 
                                                                                 fun_name = s; 
                                                                                 fun_args = [(cstor_type)]; 
                                                                                 fun_ret =  t})) }))
                        (make_selectors cstor_name cstor_type body (m + 1))
      end
        in
      let rec make_functions (s: PA.ty_var) (n: int) (lst: PA.cstor list) =
        begin match lst with
          |[] -> []
          |head::body ->
            (* print_string (head.cstor_name ^": ");
            (print_list head.cstor_ty_vars); *)
            let adt_type = (PA.Ty_app (s, []): PA.ty) (* not sure if this is the right type but it seems correct-ish*)
              in
            let constructor = (conv_statement_aux_constr({ loc = stmt.loc; (* could change to conv_statement_aux_constr maybe...*)
                                                    stmt = (Stmt_decl ({fun_ty_vars = head.cstor_ty_vars; 
                                                                                        fun_name = head.cstor_name; 
                                                                                        fun_args = List.map (fun (x, y) -> y) head.cstor_args; (* I don't really know what to put for the type here because there seems to be a list of types for each cstor - idk; Just put Ty_Bool for right now*)
                                                                                        fun_ret =  adt_type}))})) (*not really sure what body should go here: putting true for rn; I probably want to do something like " Is_a of string * term"*)
                in
            let tester =  (conv_statement_aux({ loc = stmt.loc; 
                                                stmt = (Stmt_decl ({fun_ty_vars = []; 
                                                                                    fun_name = ("is_" ^ head.cstor_name); 
                                                                                    fun_args = [(adt_type)]; (* I don't really know what to put for the type here because there seems to be a list of types for each cstor - idk; Just put Ty_Bool for right now*)
                                                                                    fun_ret =  PA.Ty_bool})) })) (*not really sure what body should go here: putting true for rn; I probably want to do something like " Is_a of string * term" *)
                in
            let selectors = (make_selectors head.cstor_name adt_type head.cstor_args 0) (* I don't really know what to put for the type here because there seems to be a list of types for each cstor - idk; Just put Ty_bool for rn*)
                in
            List.append (List.append (List.append constructor tester) selectors) (make_functions s n body)
        end
        in
      let rec analyze_ADT (lst : ((string * level) * PA.cstor list) list) =
        begin match lst with
          |[] -> []
          |((s, n), constructor_list)::body ->
                if n > 0 then (
                  errorf_ctx "cannot handle polymorphic type %s" s
                );
                (* print_list constrs; *)
                (*this is the current methodology to store all ADT information: might need to change in the future*)
                (* state.ADT_instances <- state.ADT_instances::((s, n), constructor_list);  *)
                Ctx.add_def_adt s constructor_list;
                let rec create_constructors const_list = 
                  begin match const_list with
                    |head :: body -> Ctx.add_adt_constructor s head.PA.cstor_name head;
                                      print_string ("adding the constructor " ^ head.PA.cstor_name ^ " of adt " ^ s ^ " to the context \n");
                                      (create_constructors body)
                    |[] -> ()
                  end 
                  in
                (create_constructors constructor_list);
                let declare_sort = (conv_statement_aux_adt ({ loc = stmt.loc; stmt = (Stmt_decl_sort (s, n)) })) (* need someway to save the sort type we get from here and then use it in make_functions*)
                  in
                (* print_stmts ({ loc = stmt.loc; stmt = (Stmt_decl_sort (s, n)) }); *)
                List.append
                  (List.append declare_sort (make_functions s n constructor_list))
                  (analyze_ADT body)
                (* Stmt.Stmt_data (id, n, constrs) :: analyze_ADT body *)
        end
          in
              (* state.number_terms<-(state.number_terms+1); (*want to increment the number of variables by 1 *)*)
      analyze_ADT _l
      (* end of Amar section *)
    | PA.Stmt_funs_rec _defs ->
      errorf_ctx "not implemented: definitions in %a" PA.pp_stmt stmt
        (* TODO
      let {PA.fsr_decls=decls; fsr_bodies=bodies} = defs in
      if List.length decls <> List.length bodies then (
        errorf_ctx ctx "declarations and bodies should have same length";
      );
      let defs = conv_fun_defs ctx decls bodies in
      [A.Define defs]
           *)
    | PA.Stmt_fun_def
        {PA.fr_decl={PA.fun_ty_vars=[]; fun_args=[]; fun_name; fun_ret=_}; fr_body} ->
      (* substitute on the fly *)
      let cs, rhs = conv_term_or_form fr_body in
      Ctx.add_def_const fun_name rhs;
      if cs=[] then [] else [Stmt.Stmt_assert_clauses cs] (* side conditions *)
    | PA.Stmt_fun_def
        {PA.fr_decl={PA.fun_ty_vars=[]; fun_args; fun_name; fun_ret=_}; fr_body} ->
      (* will substitute on the fly *)
      Ctx.add_def_fun fun_name fun_args fr_body;
      []
    | PA.Stmt_fun_def _
    | PA.Stmt_fun_rec _ ->
      errorf_ctx "unsupported definition: %a" PA.pp_stmt stmt
    | PA.Stmt_assert t ->
      (* TODO Federico: Rewrite term t using stored datatype declarations *)
      (* TODO Federico: Add side assertions for blasting *)

      (*Amar: Phase 2: We need somthing slightly different here, we don't have to add the side assertions here.
              Instead, we will keep track of the "depth" and add the side assertions only when we need to check-sat *)
      (* Everything between this and the next comment was written by Amar*)
      
      let rec helper t = begin match t with 
      | PA.Eq(a, b) -> max (helper a) (helper b)
      | PA.App (f, l) ->
        (* Printf.printf "Keys: %s\n" (String.concat " " (StrTbl.keys_list Ctx.t.Ctx.def_selectors)); *)
        (* TODO: see if it's a selector, not a fun *)

        begin match Ctx.find_term_sel f with
        | Some id -> 
          (* let l = List.map (conv_term_ subst) l in *)
          List.fold_left (fun acc x -> acc + helper x) 1 l
        | None -> 
          (* Phase 5!! will see if it is a constructor: if it is, will need to create a new ADT variable and recurse*)
          begin match Ctx.find_term_constr f with
            | Some id -> List.fold_left (fun acc x -> acc + helper x) 0 l
            | None -> List.fold_left (fun acc x -> acc + helper x) 0 l
          end
        end

      (*just added the below 5 lines, but it does not make sense that it would not be there*)
      (*can write necessary stuff here tmrw: I think it'll be ok*)
      in 
      let cs = conv_bool_term t in
      Log.debugf 60 (fun k->k ">>> assert clauses %a" Fmt.(Dump.(list @@ list @@ Atom.pp)) cs);
      [Stmt.Stmt_assert_clauses cs]

      (* TODO: instead of just 0 handle all the other cases *)
      | PA.Const v -> 0
      | PA.If (a,b,c) -> max (helper a) (max (helper b) (helper c))
      | PA.Let (bs,body) -> (List.fold_left (fun acc (a, b) -> acc + helper b) 0 bs) + (helper body)
      | PA.And l -> List.fold_left (fun acc x -> acc + helper x) 0 l
      | PA.Or l -> List.fold_left (fun acc x -> acc + helper x) 0 l
      | PA.Imply (a,b) -> max (helper a) (helper b)
      | PA.Distinct l -> List.fold_left (fun acc x -> acc + helper x) 0 l
      | PA.Not f -> helper f
      | PA.True -> 0
      | PA.False -> 0
      | PA.Arith (op, l) -> List.fold_left (fun acc x -> acc + helper x) 0 l
      | PA.Attr (t,_) -> helper t
      | PA.Cast (t, ty_expect) -> helper t
      | PA.HO_app _ ->
        errorf_ctx "cannot handle HO application"
      | PA.Fun _ -> errorf_ctx "cannot handle lambdas"
      | PA.Match (_lhs, _l) ->
        errorf_ctx "cannot handle match"
      | PA.Is_a _ ->
        errorf_ctx "cannot handle is-a" (* TODO *)
      | PA.Forall _ | PA.Exists _ ->
        errorf_ctx "cannot handle quantifiers" (* TODO *)
      end in

      Ctx.update_max_depth (helper t);

      (* end of Amar section*)
      Log.debugf 50 (fun k->k ">>> conv assert %a" PA.pp_term t);
      let cs = conv_bool_term t in
      (* print_string (List.map (fun x::y -> x) (List.map (fun x::y -> x) cs)); *)
      Log.debugf 60 (fun k->k ">>> assert clauses %a" Fmt.(Dump.(list @@ list @@ Atom.pp)) cs);

      [Stmt.Stmt_assert_clauses cs]
    | PA.Stmt_check_sat -> 
      (*TODO: Phase 4: Need to use the calculated depth of the function to generate all of the 
      extra statements about ADTs that we need to assert*)
      (* The statements are of four types: 1. every term must satisfy one tester
                                           2. constructors and testers play nicely with one another
                                           3. constructors and selectors play nicely with one another
                                           4. prevents cyclicality
      *)

      (* As a starting task, I will try and build the correct assertions about the adts that appear in the query so far,
      but I will not do anything about their subtrees yet: can get all of the ADT variables using (StrTbl.map_list t.def_adt_vars) *)
      
      print_string "in check_sat \n";
      Ctx.print_adt_vars ();

      (* let rec print_constructor_list (constructor_list: PA.cstor list) = 
        begin match constructor_list with
          |head :: body -> print_string (head.cstor_name ^ "\n");
                           (print_constructor_list body)
          |[] -> ()
        end
        in

      let rec check_adt_list adt_list =
        begin match adt_list with
          |head :: body -> let var_const_id, var_ty = ((StrTbl.find Ctx.t.Ctx.def_adt_vars) head) in
                           let constructor_name = ((IntTbl.find Ctx.t.Ctx.def_adt_byid) var_const_id) in
                           let constructor_list = ((StrTbl.find Ctx.t.Ctx.def_adts) constructor_name) in
                          (print_constructor_list constructor_list);
                          (check_adt_list body)
          |[] -> ()
        end

        in 
      (check_adt_list (StrTbl.keys_list Ctx.t.Ctx.def_adt_vars));  *)
      let rec make_negative_constructor_axioms (current_cstor: PA.cstor) (constructor_full_list: PA.cstor list) (var: string) = 
        begin match constructor_full_list with
          |head::body ->

            if (current_cstor.cstor_name == head.cstor_name)
            then (make_negative_constructor_axioms current_cstor body var)
            else (List.append [PA.Not (PA.App (("is_" ^ head.cstor_name), [PA.App (var, [])]))] (make_negative_constructor_axioms current_cstor body var))
          |[] -> []
        end 
      in
      let rec make_tester_axiom (constructor_list: PA.cstor list) (constructor_full_list: PA.cstor list) (var: string) = 
        begin match constructor_list with 
          |head :: body -> 
              (List.append [(PA.And (List.append [PA.App (("is_" ^ head.cstor_name), [PA.App (var, [])])] (make_negative_constructor_axioms head constructor_full_list var)))]
                (make_tester_axiom body constructor_full_list var))
          |[] -> []
        end 
      in

      let rec make_vars_for_constructor cstor_args = 
        begin match cstor_args with 
          | (name, ty):: body ->
              let new_var_name = "contrived_variable_" ^ (string_of_int Ctx.t.vars_created) in
              let new_var = (conv_statement_aux({ loc = stmt.loc; 
                                                  stmt = (Stmt_decl ({fun_ty_vars = []; 
                                                                        fun_name = new_var_name; 
                                                                        fun_args = []; 
                                                                          fun_ret =  ty})) })) 
              in 
              (* print_string (" variable: " ^ name ^ " " ^ new_var_name ^"\n"); *)
              let new_var_term = PA.App (new_var_name, []) in
              Ctx.increment_vars_created ();
              let rest_var_terms, rest_stmts = (make_vars_for_constructor body) in
              (List.append [new_var_term] rest_var_terms), (List.append new_var rest_stmts)
          |[] -> [], []
        end
    
      in

      let rec make_tester_constructor_axiom (constructor_list: PA.cstor list) (var: string) (const_name: string) =
        let var_term = PA.App (var, []) in
        begin match constructor_list with 
          | {cstor_ty_vars; cstor_name; cstor_args} :: body ->
              print_string ("in here: " ^ cstor_name ^ "\n"); 
              let contrived_vars, contrived_var_stmts = (make_vars_for_constructor cstor_args) in
              let rest_asserts, rest_stmts = (make_tester_constructor_axiom body var const_name) in
              let return_term = (PA.Eq (PA.App ("is_" ^ cstor_name, [var_term]), (PA.Eq ((PA.App (cstor_name, contrived_vars)), var_term)))) in 
              Log.debugf 1 (fun k->k ">>> printing the query we make %a" PA.pp_term return_term);
              ((List.append [return_term] rest_asserts), (List.append contrived_var_stmts rest_stmts))
          |[] -> [], []
      end 
      in

      let rec make_sel_const_ax_helper contrived_variables_before contrived_variables_next constructor_name cstor_args var = 
        let var_term = PA.App (var, []) in
        begin match contrived_variables_next with          
          |head::body -> 
            begin match cstor_args with
             |(selector_name, ty)::body2 ->
                (* print_string ("in this special case: " ^ constructor_name ^ "\n"); *)
                (List.append [(PA.Eq (PA.Eq (PA.App (selector_name, [var_term]), head), (PA.Eq ((PA.App (constructor_name, (List.append contrived_variables_before contrived_variables_next))), var_term))))]
                            (make_sel_const_ax_helper (List.append contrived_variables_before [head]) body constructor_name body2 var))
             |[] -> []
            end
          |[] -> []
        end
        in

      let rec make_selector_constructor_axiom (constructor_list: PA.cstor list) (var: string) (const_name: string) = 
        begin match constructor_list with 
          |{cstor_ty_vars; cstor_name; cstor_args} :: body -> 
            (* print_string ("in antoher special case: \n const_name: " ^ const_name ^ " \n var: " ^ var ^ "\n cstor_name: " ^ cstor_name); *)
            let contrived_vars, contrived_var_stmts = (make_vars_for_constructor cstor_args) in
            let contrived_var_axioms = (make_sel_const_ax_helper [] contrived_vars cstor_name cstor_args var) in
            let rest_axioms, rest_stmts = (make_selector_constructor_axiom body var const_name) in
            (List.append contrived_var_axioms rest_axioms), (List.append contrived_var_stmts rest_stmts)
          |[] -> [], []
      end 
      in

      let rec make_no_cycles_inner_loop var1 variable_list = 
        begin match variable_list with
          |var2 :: body ->
            conv_statement_aux({ loc = stmt.loc; 
                                stmt = (Stmt_assert (PA.Not (PA.Eq ((PA.Const var1), (PA.Const var2)))))})
          |[] -> []
        end
        in
      
      let rec make_no_cycles_axiom variable_list = 
        begin match variable_list with
          |var :: body -> (List.append (make_no_cycles_inner_loop var body) (make_no_cycles_axiom body))
          |[] -> []
        end
        
        in
      
      let rec build_variable_assertions (var_name) = 
        (* print_string ("this is the var " ^ var_name ^ "\n"); *)
        let var_const_id, var_ty = ((StrTbl.find Ctx.t.Ctx.def_adt_vars) var_name) in
        let constructor_name = ((IntTbl.find Ctx.t.Ctx.def_adt_byid) var_const_id) in
        let constructor_list = ((StrTbl.find Ctx.t.Ctx.def_adts) constructor_name) in (*TODO: see if there are helper functions to get constructors/selectors*)
        let axiom_one = conv_statement_aux({ loc = stmt.loc; (**Adding Axiom 1: every term must satisfy one tester*)  
                                              stmt = (Stmt_assert (PA.Or (make_tester_axiom constructor_list constructor_list var_name)))}) in       
        let axiom_two_asserts, axiom_two_stmts = (make_tester_constructor_axiom constructor_list var_name constructor_name) in
        let axiom_two = conv_statement_aux({ loc = stmt.loc; (* Adding Axiom 2: constructors and testers play nicely with one another*)
                                                stmt = (Stmt_assert (PA.And axiom_two_asserts))}) in
        let axiom_three, axiom_three_stmts = (make_selector_constructor_axiom constructor_list var_name constructor_name) in
        let axiom_three = conv_statement_aux({ loc = stmt.loc; (* Adding Axiom 3: constructors and selectors play nicely with one another*)
                                                stmt = (Stmt_assert (PA.And axiom_three))}) in
        (List.append (List.append (List.append axiom_one axiom_two) axiom_three) (List.append axiom_two_stmts axiom_three_stmts))
      in
      
      (*takes a list of selectors and a variable, and creates new variables that are equal to the variable*)
      (* returns a list of variables and a list of asserts about those variables*)
      let rec get_variables var_name selectors : (string list) * (statement list) = 
        begin match selectors with 
          | (selector, ty) :: body -> 
              begin match Ctx.check_def_adt selector with
                | Some (something) ->
                  let rest_vars, rest_asserts = (get_variables var_name body)
                    in
                  let new_var = (conv_statement_aux({ loc = stmt.loc; 
                                                      stmt = (Stmt_decl ({fun_ty_vars = []; 
                                                      fun_name = ("contrived_variable_" ^ (string_of_int Ctx.t.vars_created)); 
                                                      fun_args = []; 
                                                      fun_ret =  ty})) })) 
                    in 
                    (* print_string (" variable: " ^ var_name ^ " " ^ (string_of_int Ctx.t.vars_created)); *)
                  let new_var_name = "contrived_variable_" ^ (string_of_int Ctx.t.vars_created)
                    in
                  Ctx.increment_vars_created ();
                  (*want to assert that new var = selector(var_name)*)
                  let new_assertion = conv_statement_aux({ loc = stmt.loc; (* adding the fact that we can get this new variable from a selector application to var_name*)
                                                          stmt = (Stmt_assert (PA.Eq ((PA.App (selector, [(PA.Const var_name)])), (PA.Const new_var_name))))})
                    in
                  (List.append [new_var_name] rest_vars), (List.append new_var (List.append new_assertion rest_asserts))
                  (* note that we are actually appending new_var to the asserts since this is essentially an smt assert*)
                |None -> ([], [])
               end
          | [] -> ([], [])
        end
        in
      
      let rec build_new_assertions new_variables n : (string list) * (statement list) = (*TODO: write this*)
        begin match new_variables with
          | var :: body ->
              let rest_vars, rest_asserts = build_new_assertions body n in
              let new_var, new_assertion = get_constructor_list var (n - 1) in
              ((List.append new_var rest_vars), (List.append new_assertion rest_asserts))
          |[] -> [], []
        end
      

      and build_assertions_with_depth_helper (var_name : string) (constr : PA.cstor) (n : int) : (string list) * (statement list) = 
        (* print_string ("var_name: " ^ var_name ^ " n: " ^ (string_of_int n)); *)
        (* if (n = 0) then print_string "reached bottom of recursion"; *)
        if (n <= 0)
        then ([], [])
        else 
          let first_three_axioms = (build_variable_assertions var_name) in
          let new_variables, new_variable_assertions = get_variables var_name constr.PA.cstor_args in
          let more_variables, more_assertions = build_new_assertions new_variables n in
          ((List.append new_variables more_variables), (List.append first_three_axioms (List.append more_assertions new_variable_assertions) ))

      and build_assertions_with_depth (var_name : string) (n: int) constructor_list : (string list) * (statement list) = 
        (*Another issue that we never even thougth about: we just know the adt_type of the variable, not the constructor type, we then have to consider all selectors applied to it: this is kinda bad*)
        begin match constructor_list with 
          |constr :: body -> 
              let rest_vars, rest_assertions = (build_assertions_with_depth var_name n body) in
              let new_var, new_assertion = (build_assertions_with_depth_helper var_name constr n) in
              ((List.append new_var rest_vars), (List.append new_assertion rest_assertions))
        (*|var_name :: body -> List.append (build_variable_assertions var_name) (build_assertions body n)
                            (**ISSUE: not really an issue, I will just do this tmrw. Could discuss with Federico
                                      The idea is to build_variable_assertions for each element in adt_list as we do now,
                                      but also do recursive calls where we take all the subterms of var_name up to a depth n and then
                                      call build_variable_assertions on them and make sure everything is not = to their subterms  *)*)

          |[] -> ([], [])
      end
      
      and get_constructor_list (var_name : string) (n: int) = 
        print_string ("this is the var " ^ var_name ^ "\n");
        let var_const_id, var_ty = ((StrTbl.find Ctx.t.Ctx.def_adt_vars) var_name) in
        let adt_name = ((IntTbl.find Ctx.t.Ctx.def_adt_byid) var_const_id) in
        let constructor_list = ((StrTbl.find Ctx.t.Ctx.def_adts) adt_name) in 
        (build_assertions_with_depth var_name n constructor_list)

      in

      let rec build_assertions (adt_list : string list) (n : int) : statement list = 
        begin match adt_list with 
          |var_name :: body -> 
            let variables, assertions = (get_constructor_list var_name n) in
            (List.append (make_no_cycles_axiom variables) (List.append assertions (build_assertions body n)))
          |[] -> []
        end
        in

      (* let test_if_works = conv_statement_aux({ loc = stmt.loc; stmt = (Stmt_assert (PA.False))}) in *)
        
      List.append (build_assertions (StrTbl.keys_list Ctx.t.Ctx.def_adt_vars) (Ctx.t.max_depth + 1)) [Stmt.Stmt_check_sat]
    | PA.Stmt_check_sat_assuming _
    | PA.Stmt_get_assertions
    | PA.Stmt_get_option _
    | PA.Stmt_get_info _
    | PA.Stmt_get_model
    | PA.Stmt_get_proof
    | PA.Stmt_get_unsat_core
    | PA.Stmt_get_unsat_assumptions
    | PA.Stmt_get_assignment
    | PA.Stmt_reset
    | PA.Stmt_reset_assertions
    | PA.Stmt_push _
    | PA.Stmt_pop _
    | PA.Stmt_get_value _
      ->
      (* TODO: handle more of these *)
      errorf_ctx "cannot handle statement %a" PA.pp_stmt stmt

end (* why is this end here?? its from the original code, but it seems like it's just hanging -> ask Federico*)
