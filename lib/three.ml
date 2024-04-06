open Base
open Poly

module Three() = struct
  type id = string
  type ty =
    | TyBool (* Bool *)
    | TyArrow of ty * ty (* Function type: T1 -> T2 *)
    | TyVar of tv ref (* Type variable: held behind a mutable reference. *)
    | TyRecord of id * record_ty (* Record: Foo{x: Bool, y: Bool} *)
    | TyName of id (* Type name: Foo *)
  and record_ty = (id * ty) list
  and tv = (* A type variable *)
    | Unbound of id
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
    | ERecord of id * record_lit (* Foo{x = true, y = false} *)
    | EProj of exp * id (* r.y *)
  and record_lit = (id * exp) list
  type texp =
    | TEBool of bool * ty
    | TEVar of id * ty
    | TELam of id * texp * ty
    | TEApp of texp * texp * ty
    | TEIf of texp * texp * texp * ty
    | TERecord of id * tyrecord_lit * ty
    | TEProj of texp * id * ty
  and tyrecord_lit = (id * texp) list
  type prog = tycon list * exp

  let rec force (ty : ty) : ty =
    match ty with
    | TyVar { contents = Link ty } -> force ty
    | ty -> ty

  (* Utility functions for pretty printing. *)
  let ty_kind (ty : ty) =
    match ty with
    | TyBool -> "TyBool"
    | TyRecord _ -> "TyRecord"
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
    | TyVar { contents = Unbound id } -> id
    | TyArrow (from, dst) ->
      ty_pretty from ^ " -> " ^ ty_pretty dst
    | TyName name -> name
    | TyRecord (id, flds) ->
      Printf.sprintf "%s{%s}" id (ty_fields ty_pretty flds)
  
  let rec ty_debug ty =
    match ty with
    | TyBool -> "TyBool"
    | TyVar { contents = Link ty } ->
        Printf.sprintf "TyVar(Link(%s))" (ty_debug ty)
    | TyVar { contents = Unbound id } ->
        Printf.sprintf "TyVar(Unbound %s)" id
    | TyArrow(from, dst) ->
      "(" ^ ty_debug from ^ " -> " ^ ty_debug dst ^ ")"
    | TyName name -> name
    | TyRecord (id, flds) ->
      Printf.sprintf "%s{%s}" id (ty_fields ty_debug flds)

  
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
    | TERecord (_, _, ty) -> ty
    | TEProj (_, _, ty) -> ty

  (* Global state that stores a counter for generating fresh unbound type variables. *)
  let gensym_counter = ref 0

  (* Generate a fresh unbound type variable. *)
  let fresh_unbound_var () =
      let n = !gensym_counter in
      Int.incr gensym_counter;
      let tvar = "?" ^ Int.to_string n in
      TyVar (ref (Unbound tvar))

  (* Occurs check: check if a type variable occurs in a type. If it does, raise
    an exception. *)
  let rec occurs (src : tv ref) (ty : ty) : unit =
    (* Follow all the links. If we see a type variable, it will only be
      Unbound. *)
    match force ty with
    | TyVar tgt when phys_equal src tgt ->
      (* src type variable occurs in ty. *)
      raise OccursCheck
    | TyArrow(from, dst) ->
      (* Check that src occurs in the arrow type. *)
      occurs src from;
      occurs src dst;
    | _ -> ()

  (* Unify two types. If they are not unifiable, raise an exception. *)
  let rec unify (t1 : ty) (t2 : ty) : unit =
    (* Follow all the links. If we see any type variables, they will only be
      Unbound. *)
    let t1, t2 = (force t1, force t2) in
    match (t1, t2) with
    | _ when equal t1 t2 ->
      () (* The types are trivially equal (e.g. TyBool). *)
    | TyArrow (f1, d1), TyArrow (f2, d2) ->
      (* If both types are function types, unify their corresponding types
          with each other. *)
      unify f1 f2;
      unify d1 d2;
    | TyVar tv, ty | ty, TyVar tv ->
      (* If either type is a type variable, ensure that the type variable does
          not occur in the type. *)
      occurs tv ty;
      (* Link the type variable to the type. *)
      tv := Link ty
    | TyName a, TyName b when equal a b -> () (* The type names are the same. *)
    | TyRecord (id1, fds1), TyRecord (id2, fds2)
      when equal id1 id2 && equal (List.length fds1) (List.length fds2) ->
      (* Both types are records with the same name and number of fields. *)
      let unify_fld (id1, ty1) (id2, ty2) =
          if not (equal id1 id2) then raise (unify_failed ty1 ty2)
          else unify ty1 ty2
      in
      (* Unify their corresponding fields. *)
      List.iter2_exn ~f:unify_fld fds1 fds2
    | _ ->
      (* Unification has failed. *)
      raise (unify_failed t1 t2)

  let rec check env ty exp =
    match exp with
    | ERecord (tname, rec_lit) ->
        let rec_lit = List.map ~f:(fun (id, x) -> (id, infer env x)) rec_lit in
        let ty_rec =
            TyRecord (tname, List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit)
        in
        (try
            unify ty ty_rec;
            TERecord(tname, rec_lit, ty_rec)
        with UnificationFailure _ ->
            raise (type_error ty))
    | exp ->
        let texp = infer env exp in
        (try
            unify ty (typ texp);
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
      unify (typ fn) ty_arr;
      (* Return the result type. *)
      TEApp (fn, arg, ty_res)
    | EIf (cond, thn, els) ->
      (* Check that the type of condition is Bool. *)
      let cond = infer env cond in
      unify (typ cond) TyBool;
      (* Check that the types of the branches are equal to each other. *)
      let thn = infer env thn in
      let els = infer env els in
      unify (typ thn) (typ els);
      (* Return the type of one of the branches. (we'll pick the "then"
          branch) *)
      TEIf (cond, thn, els, typ thn)
    | ERecord (tname, _) ->
      (* Look up the declared type constructor for the type name on the record
          literal. *)
      let tc = lookup_tycon tname env in
      (* Turn the type constructor into a concrete record type that we can unify. *)
      let ty_dec = TyRecord(tc.name, tc.ty) in
      (* Check that the record literal matches the declared record type,
          and obtain all the typed fields. *)
      let TERecord (_, rec_lit, _) = check env ty_dec exp in
      (* Return the expression with the type as the type name. *)
      TERecord (tname, rec_lit, TyName tname)
    | EProj (rcd, fld) ->
      let rcd = infer env rcd in
      let (tname, rec_ty) = 
          match typ rcd with
          | TyName tname ->
              let tc = lookup_tycon tname env in
              (tc.name, tc.ty)
          | ty -> raise (expected_ty_error "TyName" (ty_kind ty))
      in
      (match List.Assoc.find rec_ty ~equal fld with
      | Some ty -> TEProj (rcd, fld, ty)
      | _ -> raise (missing_field fld tname))
  
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
  let open Three() in
  let prog = ([], EApp(ELam("x", EVar "x"), EBool true)) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "basic_error" =
  let open Three() in
  let prog = ([], EApp(ELam("f", EApp(EVar "f", EBool true)), EBool true)) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool -> ?1 with bool")

let%test "if" =
  let open Three() in
  let prog = ([], EIf(EBool true, EBool false, EApp(ELam("x", EVar "x"), EBool true))) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "if_error" =
  let open Three() in
  let prog = ([], EIf(EBool true, EBool false, ELam("x", EVar "x"))) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool with ?0 -> ?0")

let%test "record" =
  let open Three() in
  let prog = (
    [{name = "Foo"; ty = [("x", TyBool); ("y", TyArrow(TyBool, TyBool))] }],
    EApp(EProj(ERecord("Foo", [("x", EBool true); ("y", ELam("x", EVar "x"))]), "y"), EBool true)
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "record_error" =
  let open Three() in
  let prog = (
    [{name = "Foo"; ty = [("x", TyBool); ("y", TyArrow(TyBool, TyBool))] }],
    EProj(ERecord("Foo", [("y", EBool false)]), "y")
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type Foo{x: bool, y: bool -> bool}")