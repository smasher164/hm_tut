open Base
open Poly

module Seven() = struct
  type id = string
  (* The scope is an integer counter that holds the depth of the current
   let binding. Every unbound type variable contains the scope at which
   it was created. *)
  type scope = int
  type ty =
    | TyBool (* Bool *)
    | TyArrow of ty * ty (* Function type: T1 -> T2 *)
    | TyVar of tv ref (* Type variable: held behind a mutable reference. *)
    | TyRecord of id * record_ty (* Record: Foo{x: Bool, y: Bool} *)
    | TyName of id (* Type name: Foo *)
    | TyApp of ty list (* Type application: T1 T2 *)
  and record_ty = (id * ty) list
  and tv = (* A type variable *)
    | Unbound of id * scope
      (* Unbound type variable: Holds the type variable's unique name as well as
        the scope at which it was created. *)
    | Link of ty (* Link type variable: Holds a reference to a type. *)
  (* Type declaration/constructor. All type declarations are nominal records. *)
  type tycon = {
    name : id;
    type_params : id list;
    ty : record_ty;
  }
  (* A generic type. Should be read as forall p1..pn. ty, where p1..pn are
    the type parameters. It is separated from ty because in HM, a forall can
    only be at the top level of a type. *)
  type generic_ty = {
      type_params: id list;
      ty : ty;
  }
  type bind =
    | VarBind of generic_ty (* A variable binding maps to a generic type. *)
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
    | ELet of let_decl * exp (* let x : <type-annotation> = <exp> in <exp> *)
    | ELetRec of let_decl list * exp (* let rec <decls> in <exp> *)
  and record_lit = (id * exp) list
  and let_decl = id * generic_ty option * exp
  type texp =
    | TEBool of bool * ty
    | TEVar of id * ty
    | TELam of id * texp * ty
    | TEApp of texp * texp * ty
    | TEIf of texp * texp * texp * ty
    | TERecord of id * tyrecord_lit * ty
    | TEProj of texp * id * ty
    | TELet of tlet_decl * texp * ty
    | TELetRec of tlet_decl list * texp * ty
  and tyrecord_lit = (id * texp) list
  and tlet_decl = id * generic_ty option * texp
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
    | TyApp _ -> "TyApp"

  let ty_fields f flds =
    flds
    |> List.map ~f:(fun (id, ty) -> id ^ ": " ^ f ty)
    |> String.concat ~sep:", "

  let rec ty_pretty ty =
    match force ty with
    | TyBool -> "bool"
    | TyVar { contents = Link _ } -> failwith "unexpected: Link"
    | TyVar { contents = Unbound(id, _) } -> id
    | TyArrow (from, dst) ->
      ty_pretty from ^ " -> " ^ ty_pretty dst
    | TyName name -> name
    | TyRecord (id, flds) ->
      Printf.sprintf "%s{%s}" id (ty_fields ty_pretty flds)
    | TyApp app -> String.concat ~sep:" " (List.map app ~f:ty_pretty)
  
  let rec ty_debug ty =
    match ty with
    | TyBool -> "TyBool"
    | TyVar { contents = Link ty } ->
        Printf.sprintf "TyVar(Link(%s))" (ty_debug ty)
    | TyVar { contents = Unbound(id,scope) } ->
        Printf.sprintf "TyVar(Unbound(%s,%d))" id scope
    | TyArrow(from, dst) ->
      "(" ^ ty_debug from ^ " -> " ^ ty_debug dst ^ ")"
    | TyName name -> name
    | TyRecord (id, flds) ->
      Printf.sprintf "%s{%s}" id (ty_fields ty_debug flds)
    | TyApp app -> String.concat ~sep:" " (List.map app ~f:ty_debug)

  
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
  let lookup_var_type name (e : env) : generic_ty =
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
    | TELet (_, _, ty) -> ty
    | TELetRec (_, _, ty) -> ty

  (* Global state that stores a counter for generating fresh unbound type variables. *)
  let gensym_counter = ref 0
  (* Global state that stores the current scope. *)
  let current_scope = ref 1
  let enter_scope () = Int.incr current_scope
  let leave_scope () = Int.decr current_scope

  (* Generate a fresh unbound type variable with a unique name and
   the current scope. *)
  let fresh_unbound_var () =
    let n = !gensym_counter in
    Int.incr gensym_counter;
    let tvar = "?" ^ Int.to_string n in
    TyVar (ref (Unbound (tvar, !current_scope)))

  (* Occurs check: check if a type variable occurs in a type. If it does, raise
    an exception. *)
  let rec occurs (src : tv ref) (ty : ty) : unit =
    (* Follow all the links. If we see a type variable, it will only be
      Unbound. *)
    match force ty with
    | TyVar tgt when phys_equal src tgt ->
      (* src type variable occurs in ty. *)
      raise OccursCheck
    | TyVar ({ contents = Unbound (id, tgt_scope) } as tgt) ->
      (* Grabbed src and tgt's scopes. *)
      let { contents = Unbound(_, src_scope) } = src in
      (* Compute the minimum of their scopes (the outermost scope). *)
      let min_scope = min src_scope tgt_scope in
      (* Update the tgt's scope to be the minimum. *)
      tgt := Unbound (id, min_scope)
    | TyArrow(from, dst) ->
      (* Check that src occurs in the arrow type. *)
      occurs src from;
      occurs src dst;
    | TyRecord (_, flds) ->
      (* Check that src occurs in the field types. *)
      List.iter flds ~f:(fun (_, ty) -> occurs src ty)
    | TyApp app ->
      (* Check that src occurs in the type application. *)
      List.iter app ~f:(occurs src)
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
          not occur in the type. Update the scopes while you're at it. *)
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
    | TyApp app1, TyApp app2 when List.length app1 = List.length app2 ->
      (* If both types are type applications, unify their corresponding types
          with each other. *)
      List.iter2_exn app1 app2 ~f:unify
    | _ ->
      (* Unification has failed. *)
      raise (unify_failed t1 t2)

(* Create and initialize a hash table of ids and fresh unbound type
   variables. *)
   let create_table_for_type_params (l: id list) : (id, ty) Hashtbl.t =
    match
        Hashtbl.create_mapped
            (module String)
            ~get_key:Fn.id
            ~get_data:(fun _ -> fresh_unbound_var ())
            l
    with
    | `Ok tbl -> tbl
    | `Duplicate_keys _ -> failwith "unreachable: duplicate keys in type params"

  (* The environment stores generic types, but sometimes, we need to
   associate a non-generalized type to a variable. This function
   wraps a type into a generic type. *)
  let dont_generalize ty : generic_ty = { type_params = []; ty }
  
  let gen (ty: ty) : generic_ty =
    let type_params = Hash_set.create (module String) in
    let rec gen' ty =
        match force ty with
        | TyVar { contents = Unbound (id, scope) } when scope > !current_scope ->
            Hash_set.add type_params id;
            TyName id
        | TyArrow (from, dst) ->
            let from = gen' from in
            let dst = gen' dst in
            TyArrow(from, dst)
        | TyRecord (id, flds) ->
            let flds = List.map ~f:(fun (id, ty) -> (id, gen' ty)) flds in
            TyRecord (id, flds)
        | TyApp app ->
          let app = List.map app ~f:gen' in
          TyApp app
        | ty -> ty
    in
    let ty = gen' ty in
    let type_params = Hash_set.to_list type_params |> List.sort ~compare in
    { type_params; ty }
  
  (* Instantiate a generic type by replacing all the type parameters
   with fresh unbound type variables. Ensure that the same ID gets
   mapped to the same unbound type variable by using an (id, ty) Hashtbl. *)
   let inst ?(tbl: (id, ty) Hashtbl.t option) (gty: generic_ty) : ty =
    let tbl =
      (* If a hash table is provided, use it. Otherwise, create a new one. *)
      match tbl with
      | None -> create_table_for_type_params gty.type_params
      | Some tbl -> tbl
  in
    let rec inst' (ty: ty) =
        match force ty with
        | TyName id as ty -> (
          (* The quantified type variable will be referred to by a type name. *)
          match Hashtbl.find tbl id with
          | Some tv -> tv
          | None -> ty)
        | TyArrow (from, dst) ->
          (* Instantiate the type vars in the arrow type. *)
          let from_inst = inst' from in
          let dst_inst = inst' dst in
          TyArrow (from_inst, dst_inst)
        | TyRecord (id, flds) ->
          (* Instantiate the type vars in the record fields. *)
          let inst_fld (id, ty) = (id, inst' ty) in
          TyRecord (id, List.map ~f:inst_fld flds)
        | TyApp app ->
          (* Instantiate the type vars in the type application. *)
          TyApp (List.map app ~f:inst')
        | ty -> ty
    in
    if Hashtbl.is_empty tbl then gty.ty else inst' gty.ty

  let inst_tycon (tc: tycon) : ty =
    (* No type parameters, so all we need is the type name. *)
    if List.is_empty tc.type_params then TyName tc.name
    else
        (* Map over the type parameters to build up a TyApp with fresh unbound
            variables. *)
        TyApp
            (TyName tc.name
            :: List.map tc.type_params ~f:(fun _ -> fresh_unbound_var ()))

  let apply_type (env: env) (ty: ty) : ty =
    match ty with
    | TyName id ->
      let tc = lookup_tycon id env in
      TyRecord (tc.name, tc.ty)
    | TyApp (TyName id :: type_args) ->
      let tc = lookup_tycon id env in
      let tbl =
        match List.zip tc.type_params type_args with
        | Ok alist -> Hashtbl.of_alist_exn (module String) alist
        | Unequal_lengths ->
            failwith "incorrect number of arguments in type application"
      in
      inst ~tbl
        { type_params = tc.type_params; ty = TyRecord (tc.name, tc.ty) }
    | _ -> failwith "expected TyName or TyApp"

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
      (* instantiate its type by replacing all of its quantified type
         variables with fresh unbound type variables.*)
      TEVar (name, inst var_ty)
    | ELam (param, body) ->
      (* Instantiate a fresh type variable for the lambda parameter, and
          extend the environment with the param and its type. *)
      let ty_param = fresh_unbound_var () in
      let env' = (param, VarBind (dont_generalize ty_param)) :: env in
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
    | ERecord (tname, rec_lit) ->
      (* Look up the declared type constructor for the type name on the record
          literal. *)
      let tc = lookup_tycon tname env in
      (* Instantiate the type constructor into a type with fresh unbound
          variables. *)
      let ty_app = inst_tycon tc in
      (* Apply the type application to get a concrete record type that we can
          unify. *)
      let ty_dec = apply_type env ty_app in
      (* Check that the record literal matches the declared record type,
          and obtain all the typed fields. *)
      let TERecord (_, rec_lit, _) = check env ty_dec exp in
      (* Return the expression with its type as a TyName or a TyApp. *)
      TERecord (tname, rec_lit, ty_app)
    | EProj (rcd, fld) ->
      (* Infer the type of the expression we're projecting on. *)
      let rcd = infer env rcd in
      (* Concretize the type in case it's a type application. *)
      let TyRecord(tname, rec_ty) = apply_type env (typ rcd) in
      (* Check that it has the field we're accessing. *)
      (match List.Assoc.find rec_ty ~equal fld with
      (* Return the field's type in the record. *)
      | Some ty -> TEProj (rcd, fld, ty)
      | _ -> raise (missing_field fld tname))
    | ELet ((id, ann, rhs), body) ->
      enter_scope();
      let rhs =
          match ann with
          | Some ann -> check env (inst ann) rhs
          | None -> infer env rhs
      in
      leave_scope();
      let ty_gen = gen (typ rhs) in
      let env = (id, VarBind ty_gen) :: env in
      let body = infer env body in
      TELet ((id, ann, rhs), body, typ body)
    | ELetRec (decls, body) ->
      enter_scope();
      let deduped_defs = Hash_set.create (module String) in
      let env_decls = List.map decls ~f:(fun (id, ann, _) ->
          match Hash_set.strict_add deduped_defs id with
          | Ok _ ->
              let ty_decl =
                  match ann with
                  | Some ann -> inst ann
                  | None -> fresh_unbound_var()
              in (id, VarBind (dont_generalize ty_decl))
          | Error _ -> raise (duplicate_definition id) 
      ) in
      let env' = env_decls @ env in
      let decls = List.map2_exn env_decls decls ~f:(
          fun (id, VarBind ty_bind) (_, ann, rhs) ->
              let rhs = check env' (inst ty_bind) rhs in
              (id, ann, rhs))
      in
      leave_scope();
      let generalized_bindings =
          List.map ~f:(fun (id, _, rhs) -> (id, VarBind (gen (typ rhs)))) decls
      in
      let env = generalized_bindings @ env in
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
  let open Seven() in
  let prog = ([], EApp(ELam("x", EVar "x"), EBool true)) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "basic_error" =
  let open Seven() in
  let prog = ([], EApp(ELam("f", EApp(EVar "f", EBool true)), EBool true)) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool -> ?1 with bool")

let%test "if" =
  let open Seven() in
  let prog = ([], EIf(EBool true, EBool false, EApp(ELam("x", EVar "x"), EBool true))) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "if_error" =
  let open Seven() in
  let prog = ([], EIf(EBool true, EBool false, ELam("x", EVar "x"))) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool with ?0 -> ?0")

let%test "record" =
  let open Seven() in
  let prog = (
    [{name = "Foo"; type_params = []; ty = [("x", TyBool); ("y", TyArrow(TyBool, TyBool))] }],
    EApp(EProj(ERecord("Foo", [("x", EBool true); ("y", ELam("x", EVar "x"))]), "y"), EBool true)
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "record_error" =
  let open Seven() in
  let prog = (
    [{name = "Foo"; type_params = []; ty = [("x", TyBool); ("y", TyArrow(TyBool, TyBool))] }],
    EProj(ERecord("Foo", [("y", EBool false)]), "y")
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type Foo{x: bool, y: bool -> bool}")

let%test "let" =
  let open Seven() in
  let prog = (
    [{name = "A"; type_params = []; ty = [("x", TyBool)]}],
    ELet(("r", None, ERecord("A", [("x", EBool true)])), EProj(EVar "r", "x"))
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "let_ann" =
  let open Seven() in
  let prog = (
    [{name = "A"; type_params = []; ty = []}],
    ELet(("x", Some { type_params = []; ty = TyName "A" }, EBool true), EVar "x")
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type A")

let%test "let_rec" =
  let open Seven() in
  let prog = ([], ELetRec(
    [("f", None, ELam("x", EIf(EVar "x", EApp(EVar "g", EVar "x"), EVar "x")));
    ("g", None, ELam("x", EIf(EVar "x", EApp(EVar "f", EVar "x"), EVar "x")))],
    EApp(EVar "f", EBool true)
  ))
  in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "let_rec_error" =
  let open Seven() in
  let prog = (
    [{name = "A"; type_params = []; ty = []}],
    ELetRec(
    [("f", None, ELam("x", EIf(EVar "x", EApp(EVar "g", EVar "x"), EVar "x")));
    ("g", None, ELam("x", EIf(EVar "x", EApp(EVar "f", EVar "x"), ERecord("A", []))))],
    EApp(EVar "f", EBool true))
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool with A")

let%test "let_gen" =
  let open Seven() in
  let prog = (
    [{name = "A"; type_params = []; ty = []}],
    ELet(("f", None, ELam("x", EVar "x")),
      ELet(("_", None, EApp(EVar "f", ERecord("A", []))),
        EApp(EVar "f", EBool true)))
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "fix" =
  let open Seven() in
  let prog = (
    [],
    ELetRec([("fix", None, ELam("f", ELam("x", EApp(EApp(EVar "f", EApp(EVar "fix", EVar "f")), EVar "x"))))],
    EApp(EVar "fix", ELam("f", ELam("arg", EIf(EVar "arg", EApp(EVar "f", EBool false), EBool true)))))
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool -> bool"

let%test "let_gen_ann" =
  let open Seven() in
  let prog = (
    [{name = "A"; type_params = []; ty = []}],
    ELet(("f", Some {type_params = ["'a"]; ty = TyArrow(TyName "'a", TyBool)}, ELam("x", EBool true)),
      EApp(EVar "f", ERecord("A", []))
    )
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "bool"

let%test "let_gen_error" = 
  let open Seven() in
  let prog = (
    [{name = "A"; type_params = []; ty = []}],
    ELet(("f", Some {type_params = ["'a"]; ty = TyArrow(TyName "'a", TyName "A")}, ELam("x", EBool true)), EApp(EVar "f", EBool true))
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type ?1 -> A")

let%test "let_gen_scope_error" =
  let open Seven() in
  let prog = (
    [],
    EApp(EApp(ELam("x", ELet(("y", None, EVar "x"), EVar "y")), EBool true), EBool true)
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool with bool -> ?2")

let%test "generic_tycon" =
  let open Seven() in
  let prog = (
    [{name = "box"; type_params = ["'a"]; ty = [("x", TyName "'a")]}],
    ELet(("r", None, ERecord("box", [("x", EBool true)])), EVar "r")
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "box bool"

let%test "generic_tycon_let_gen" =
  let open Seven() in
  let prog = (
    [{name = "box"; type_params = ["'a"]; ty = [("x", TyName "'a")]}],
    ELet(("f", None, ELam("v",
      ELet(("r", None, ERecord("box", [("x", ERecord("box", [("x", EVar "v")]))])),
        EProj(EVar "r", "x")))),
      EApp(EVar "f", EBool true))
  ) in
  let x = typecheck_prog prog in
  let t = typ x in
  Poly.equal (ty_pretty t) "box bool"

let%test "generic_tycon_error" =
  let open Seven() in
  let prog = (
    [{name = "box"; type_params = ["'a"]; ty = [("x", TyName "'a"); ("y", TyBool)]}],
    EProj(ERecord("box", [("x", EBool true)]), "x")
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type box{x: ?0, y: bool}")