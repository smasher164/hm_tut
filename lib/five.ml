open Base
open Poly

module Five() = struct
  type id = string
  type ty =
    | TyBool (* Bool *)
    | TyArrow of ty * ty (* Function type: T1 -> T2 *)
    | TyVar of tv ref (* Type variable: held behind a mutable reference. *)
    | TyName of id (* Type name: Foo *)
  and record_ty = (id * ty) list
  and tv = (* A type variable *)
    | Unbound of id * (record_ty option)
      (* Unbound type variable: Holds the type variable's unique name. *)
    | Link of ty (* Link type variable: Holds a reference to a type. *)
  (* Type declaration/constructor. All type declarations are nominal records. *)
  type tycon = {
    name : id;
    ty : record_ty;
  }  
  type bind =
    | VarBind of ty (* A variable binding maps to a type. *)
    | TypeBind of tycon (* A type binding maps to a type constructor. *)
  type env = (id * bind) list
  type exp =
    | EBool of bool (* true/false *)
    | EVar of id (* x *)
    | ELam of id * exp (* fun x -> x *)
    | EApp of exp * exp (* f arg *)
    | EIf of exp * exp * exp (* if <exp> then <exp> else <exp> *)
    | ERecord of record_lit (* {x = true, y = false} *)
    | EProj of exp * id (* r.y *)
    | ELet of let_decl * exp (* let x : <type-annotation> = <exp> in <exp> *)
    | ELetRec of let_decl list * exp (* let rec <decls> in <exp> *)
  and record_lit = (id * exp) list
  and let_decl = id * ty option * exp
  type texp =
    | TEBool of bool * ty
    | TEVar of id * ty
    | TELam of id * texp * ty
    | TEApp of texp * texp * ty
    | TEIf of texp * texp * texp * ty
    | TERecord of tyrecord_lit * ty
    | TEProj of texp * id * ty
    | TELet of tlet_decl * texp * ty
    | TELetRec of tlet_decl list * texp * ty
  and tyrecord_lit = (id * texp) list
  and tlet_decl = id * ty option * texp
  type prog = tycon list * exp

  let rec force (ty : ty) : ty =
    match ty with
    | TyVar { contents = Link ty } -> force ty
    | ty -> ty

  (* Utility functions for pretty printing. *)
  let ty_kind (ty : ty) =
    match ty with
    | TyBool -> "TyBool"
    | TyVar _ -> "TyVar"
    | TyArrow _ -> "TyArrow"
    | TyName _ -> "TyName"

  let ty_fields f flds =
    flds
    |> List.map ~f:(fun (id, ty) -> id ^ ": " ^ f ty)
    |> String.concat ~sep:", "

  let rec ty_pretty ty =
    match force ty with
    | TyBool -> "bool"
    | TyVar { contents = Link _ } -> failwith "unexpected: Link"
    | TyVar { contents = Unbound(id, None) } -> id
    | TyVar { contents = Unbound(id, Some flds) } ->
      Printf.sprintf "%s{%s}" id (ty_fields ty_pretty flds)
    | TyArrow (from, dst) ->
      ty_pretty from ^ " -> " ^ ty_pretty dst
    | TyName name -> name
  
  let rec ty_debug ty =
    match ty with
    | TyBool -> "TyBool"
    | TyVar { contents = Link ty } ->
        Printf.sprintf "TyVar(Link(%s))" (ty_debug ty)
    | TyVar { contents = Unbound(id, None) } -> Printf.sprintf "TyVar(Unbound %s)" id
    | TyVar { contents = Unbound(id, Some flds) } ->
      Printf.sprintf "TyVar(Unbound(%s, %s))" id (ty_fields ty_debug flds)
    | TyArrow(from, dst) ->
      "(" ^ ty_debug from ^ " -> " ^ ty_debug dst ^ ")"
    | TyName name -> name

  
  exception Undefined of string
  exception DuplicateDefinition of string
  exception MissingField of string
  exception UnificationFailure of string
  exception OccursCheck
  exception TypeError of string
  exception Expected of string

  let undefined_error kind name =
      Undefined (Printf.sprintf "%s %s not defined" kind name)

  let duplicate_definition def =
    DuplicateDefinition (Printf.sprintf "duplicate definition of %s" def)

  let unify_failed t1 t2 =
    UnificationFailure
      (Printf.sprintf "failed to unify type %s with %s" (ty_pretty t1)
          (ty_pretty t2))

  let missing_field field inside =
    MissingField (Printf.sprintf "missing field %s in %s" field inside)

  let type_error ty =
    TypeError(Printf.sprintf "expression does not have type %s" (ty_pretty ty))

  let expected_ty_error expected got =
    Expected (Printf.sprintf "expected type %s, got %s" expected got)

  (* Lookup a variable's type in the environment. *)
  let lookup_var_type name (e : env) : ty =
    match List.Assoc.find e ~equal name with
    | Some (VarBind t) -> t
    | _ -> raise (undefined_error "variable" name)

  (* Lookup a type constructor in the environment. *)
  let lookup_tycon name (e : env) : tycon =
    match List.Assoc.find e ~equal name with
    | Some (TypeBind t) -> t
    | _ -> raise (undefined_error "type" name)

  (* Get the type of a typed expression. *)
  let typ (texp : texp) : ty =
    match texp with
    | TEBool _ -> TyBool
    | TEVar (_, ty) -> ty
    | TEApp (_, _, ty) -> ty
    | TELam (_, _, ty) -> ty
    | TEIf (_, _, _, ty) -> ty
    | TERecord (_, ty) -> ty
    | TEProj (_, _, ty) -> ty
    | TELet (_, _, ty) -> ty
    | TELetRec (_, _, ty) -> ty

  (* Global state that stores a counter for generating fresh unbound type variables. *)
  let gensym_counter = ref 0

  (* Generate a fresh unbound type variable. *)
  let fresh_unbound_var ?row () =
    let n = !gensym_counter in
    Int.incr gensym_counter;
    let tvar = "?" ^ Int.to_string n in
    TyVar (ref (Unbound(tvar, row)))

  let row_iter (row: record_ty option) f =
    Option.iter row ~f:(fun row -> List.iter row ~f)

  let rec union_rows env (row_a: record_ty option) (row_b: record_ty option) : record_ty option =
    match (row_a, row_b) with
    | None, None -> None
    | None, Some flds | Some flds, None -> Some flds
    | Some row_a, Some row_b ->
      Some (List.dedup_and_sort (row_a @ row_b) ~compare:(fun (f1,t1) (f2,t2) ->
        if f1 = f2 then (unify env t1 t2; 0)
        else Poly.compare (f1,t1) (f2,t2)))

  (* Occurs check: check if a type variable occurs in a type. If it does, raise
    an exception. *)
  and occurs (src : tv ref) (ty : ty) : unit =
    (* Follow all the links. If we see a type variable, it will only be
       Unbound. *)
    match force ty with
    | TyVar tgt when src == tgt -> raise OccursCheck
    | TyVar { contents = Unbound(_, tgt_row) } ->
      row_iter tgt_row (fun (_, ty) -> occurs src ty)
    | TyArrow(from, dst) ->
      (* Check that src occurs in the arrow type. *)
      occurs src from;
      occurs src dst;
    | _ -> ()

  (* Unify two types. If they are not unifiable, raise an exception. *)
  and unify env (t1 : ty) (t2 : ty) : unit =
    (* Follow all the links. If we see any type variables, they will only be
      Unbound. *)
    let t1, t2 = (force t1, force t2) in
    match (t1, t2) with
    | _ when equal t1 t2 ->
      () (* The types are trivially equal (e.g. TyBool). *)
    | TyArrow (f1, d1), TyArrow (f2, d2) ->
      (* If both types are function types, unify their corresponding types
          with each other. *)
      unify env f1 f2;
      unify env d1 d2;
    | TyVar tv, ty | ty, TyVar tv ->
      let Unbound(_, tv_row) = !tv in
      (match ty with
      | TyName tname ->
        let tc = lookup_tycon tname env in
        row_iter tv_row (fun (fx,tx) ->
          (* Check that the type constructor contains all fields in tv_row *)
          if not (List.exists tc.ty ~f:(fun (f,t) -> f = fx && (unify env t tx; true))) then
            raise (missing_field fx tc.name)
        )
      | TyBool when Option.is_some tv_row -> raise (unify_failed t1 t2)
      | TyVar other when tv != other ->
        (* Union the rows of these two distinct type variables. *)
        let Unbound(id, other_row) = !other in
        row_iter other_row (fun (_, ty) -> occurs tv ty);
        let row = union_rows env tv_row other_row in
        other := Unbound(id, row)
      | _ ->
        (* If either type is a type variable, ensure that the type variable does
            not occur in the type. *)
        occurs tv ty);
      (* Link the type variable to the type. *)
      tv := Link ty
    | TyName a, TyName b when equal a b -> () (* The type names are the same. *)
    | _ ->
      (* Unification has failed. *)
      raise (unify_failed t1 t2)

  let rec check env ty exp =
    let texp = infer env exp in
    (try
        unify env ty (typ texp);
        texp
    with UnificationFailure _ ->
        raise (type_error ty))
  
  and infer (env : env) (exp : exp) : texp =
    match exp with
    | EBool b -> TEBool (b, TyBool) (* A true/false value is of type Bool. *)
    | EVar name ->
      (* Variable is being used. Look up its type in the environment, *)
      let var_ty = lookup_var_type name env in
      TEVar (name, var_ty)
    | ELam (param, body) ->
      (* Instantiate a fresh type variable for the lambda parameter, and
          extend the environment with the param and its type. *)
      let ty_param = fresh_unbound_var () in
      let env' = (param, VarBind ty_param) :: env in
      (* Typecheck the body of the lambda with the extended environment. *)
      let body = infer env' body in
      (* Return a synthesized arrow type from the parameter to the body. *)
      TELam (param, body, TyArrow ( ty_param, typ body ))
    | EApp (fn, arg) ->
      (* To typecheck a function application, first infer the types of the
          function and the argument. *)
      let fn = infer env fn in
      let arg = infer env arg in
      (* Instantiate a fresh type variable for the result of the application,
          and synthesize an arrow type going from the argument to the
          result. *)
      let ty_res = fresh_unbound_var () in
      let ty_arr = TyArrow (typ arg, ty_res ) in
      (* Unify it with the function's type. *)
      unify env (typ fn) ty_arr;
      (* Return the result type. *)
      TEApp (fn, arg, ty_res)
    | EIf (cond, thn, els) ->
      (* Check that the type of condition is Bool. *)
      let cond = infer env cond in
      unify env (typ cond) TyBool;
      (* Check that the types of the branches are equal to each other. *)
      let thn = infer env thn in
      let els = infer env els in
      unify env (typ thn) (typ els);
      (* Return the type of one of the branches. (we'll pick the "then"
          branch) *)
      TEIf (cond, thn, els, typ thn)
    | ERecord rec_lit ->
      let rec_lit = List.map rec_lit ~f:(fun (id, x) -> (id, infer env x)) in
      let row = List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit in
      let ty = fresh_unbound_var ~row () in
      TERecord (rec_lit, ty)
    | EProj (rcd, fld) ->
      let rcd = infer env rcd in
      (match typ rcd with
      | TyName tname ->
        let tc = lookup_tycon tname env in
        (match List.Assoc.find tc.ty ~equal fld with
        | Some ty -> TEProj (rcd, fld, ty)
        | _ -> raise (missing_field fld tc.name))
      | TyVar ({ contents = Unbound(id, row) } as tv) ->
        let fld_ty = fresh_unbound_var() in
        let row = union_rows env row (Some [(fld, fld_ty)]) in
        tv := Unbound(id, row);
        TEProj(rcd, fld, fld_ty)
      | ty -> raise (expected_ty_error "TyName or TyVar" (ty_kind ty)))
    | ELet ((id, ann, rhs), body) ->
      let rhs =
          match ann with
          | Some ann -> check env ann rhs
          | None -> infer env rhs
      in
      let env = (id, VarBind (typ rhs)) :: env in
      let body = infer env body in
      TELet ((id, ann, rhs), body, typ body)
    | ELetRec (decls, body) ->
      let deduped_defs = Hash_set.create (module String) in
      let env_decls = List.map decls ~f:(fun (id, ann, _) ->
          match Hash_set.strict_add deduped_defs id with
          | Ok _ ->
              let ty_decl =
                  match ann with
                  | Some ann -> ann
                  | None -> fresh_unbound_var()
              in (id, VarBind ty_decl)
          | Error _ -> raise (duplicate_definition id) 
      ) in
      let env = env_decls @ env in
      let decls : tlet_decl list = List.map2_exn env_decls decls ~f:(
          fun (id, VarBind ty_bind) (_, ann, rhs) ->
              let trhs = check env ty_bind rhs in
              (id, ann, trhs))
      in
      let body = infer env body in
      TELetRec (decls, body, typ body)
  
  let typecheck_prog ((tl,exp): prog) : texp =
    let deduped_defs = Hash_set.create (module String) in
    let env = List.map tl ~f:(fun tc ->
      match Hash_set.strict_add deduped_defs tc.name with
      | Ok _ -> (tc.name, TypeBind tc)
      | Error _ -> raise (duplicate_definition tc.name))
    in infer env exp
end

let assert_raises f e =
  try
    ignore (f ());
    false
  with exn -> equal exn e

let%test "basic" =
  let open Five() in
  let prog = ([], EApp(ELam("x", EVar "x"), EBool true)) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "basic_error" =
  let open Five() in
  let prog = ([], EApp(ELam("f", EApp(EVar "f", EBool true)), EBool true)) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool -> ?1 with bool")

let%test "if" =
  let open Five() in
  let prog = ([], EIf(EBool true, EBool false, EApp(ELam("x", EVar "x"), EBool true))) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "if_error" =
  let open Five() in
  let prog = ([], EIf(EBool true, EBool false, ELam("x", EVar "x"))) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool with ?0 -> ?0")

let%test "record" =
  let open Five() in
  let prog = (
    [{name = "Foo"; ty = [("x", TyBool); ("y", TyArrow(TyBool, TyBool))] }],
    EApp(EProj(ERecord([("x", EBool true); ("y", ELam("x", EVar "x"))]), "y"), EBool true)
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "record_anonymous" =
  let open Five() in
  let prog = ([], EProj(ERecord([("y", EBool false)]), "y")) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "row" =
  let open Five() in
  let prog = (
    [{name = "Foo"; ty = [("y", TyArrow(TyBool, TyBool))]}],
    EApp(EApp(ELam("r", EProj(EVar "r", "y")), ERecord([("y", ELam("x", EVar "x"))])), EBool true)
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "row2" =
  let open Five() in
  let prog = (
    [{name = "Foo"; ty = [("f", TyArrow(TyBool, TyBool))]};
      {name = "Bar"; ty = [("x", TyBool)]}],
    EApp(
      EApp(ELam("r1", ELam("r2", EApp(EProj(EVar "r2", "f"), EProj(EVar "r1", "x")))),
      ERecord([("x", EBool true)])),
    ERecord([("f", ELam("x", EVar "x"))]))
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "let" =
  let open Five() in
  let prog = (
    [{name = "A"; ty = [("x", TyBool)]}],
    ELet(("r", None, ERecord [("x", EBool true)]), EProj(EVar "r", "x"))
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "let_nogen" =
  let open Five() in
  let prog = ([],
    ELet(("f", None, ELam("x", EVar "x")),
      ELet(("_", None, EApp(EVar "f", ERecord[])),
        EApp(EVar "f", EBool true)))
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type ?2{} with bool")

let%test "let_ann" =
  let open Five() in
  let prog = (
    [{name = "A"; ty = []}],
    ELet(("x", Some(TyName "A"), EBool true), EVar "x")
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type A")

let%test "let_rec" =
  let open Five() in
  let prog = ([], ELetRec(
    [("f", None, ELam("x", EIf(EVar "x", EApp(EVar "g", EVar "x"), EVar "x")));
    ("g", None, ELam("x", EIf(EVar "x", EApp(EVar "f", EVar "x"), EVar "x")))],
    EApp(EVar "f", EBool true)
  )) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "let_rec_error" =
  let open Five() in
  let prog = (
    [{name = "A"; ty = []}],
    ELetRec(
    [("f", None, ELam("x", EIf(EVar "x", EApp(EVar "g", EVar "x"), EVar "x")));
    ("g", Some (TyArrow(TyBool, TyName "A")), ELam("x", EIf(EVar "x", EApp(EVar "f", EVar "x"), ERecord[])))],
    EApp(EVar "f", EBool true))
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type A with bool")