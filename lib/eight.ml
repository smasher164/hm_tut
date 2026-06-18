open Base
open Poly
open Mini_ml

module Eight() = struct
  type id = string
  (* The scope is an integer counter that holds the depth of the current
    let binding. Every unbound type variable contains the scope at which
    it was created. *)
  type scope = int
  type ty =
    | TyBool (* Bool *)
    | TyArrow of ty * ty (* Function type: T1 -> T2 *)
    | TyVar of tv ref (* Type variable: held behind a mutable reference. *)
    | TyName of id (* Type name: a tycon (with no args) or a rigid type variable. *)
    | TyApp of ty list (* Type application: head :: args, e.g. TyApp[TyName "box"; TyBool] *)
  and record_ty = (id * ty) list
  and row_constraint =
    | NoRow (* No row constraint. *)
    | OpenRow of record_ty (* Must contain at least these fields (from EProj/EWith). *)
    | ClosedRow of record_ty (* Must contain exactly these fields (from ERecord). *)
  and tv = (* A type variable *)
    | Unbound of id * row_constraint * scope
      (* Unbound type variable: Holds the type variable's unique name, any
        row constraint, and the scope at which it was created. *)
    | Link of ty (* Link type variable: Holds a reference to a type. *)
  (* Type declaration/constructor with type parameters. All type declarations are nominal records. *)
  type tycon = {
    name : id;
    type_params : id list;
    ty : record_ty;
  }
  (* A generic type. Should be read as forall p1::r1..pn::rn. ty, where each
    pi is a type parameter and ri its row constraint (NoRow for plain
    parameters). It is separated from ty because in HM, a forall can
  only be at the top level of a type. *)
  type generic_ty = {
    type_params : (id * row_constraint) list;
    ty : ty;
  }
  type bind =
    | VarBind of generic_ty (* A variable binding maps to a generic type. *)
    | TypeBind of tycon (* A type binding maps to a type constructor. *)
    | TypeVarBind of row_constraint
      (* A type variable binding marks some rigid type and its corresponding row constraints. *)
  type env = (id * bind) list
  type exp =
    | EBool of bool (* true/false *)
    | EVar of id (* x *)
    | ELam of id * exp (* fun x -> x *)
    | EApp of exp * exp (* f arg *)
    | EIf of exp * exp * exp (* if <exp> then <exp> else <exp> *)
    | ERecord of record_lit (* {x = true, y = false} *)
    | EWith of exp * record_lit (* { r with x = true } *)
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
    | TERecord of tyrecord_lit * ty
    | TEWith of texp * tyrecord_lit * ty
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
  let ty_fields f flds =
    flds
    |> List.map ~f:(fun (id, ty) -> id ^ ": " ^ f ty)
    |> String.concat ~sep:", "

  let print_row f row =
    match row with
    | NoRow -> "NoRow"
    | OpenRow flds -> Printf.sprintf "{%s, ...}" (ty_fields f flds)
    | ClosedRow flds -> Printf.sprintf "{%s}" (ty_fields f flds)

  let rec ty_pretty ty =
    match force ty with
    | TyBool -> "bool"
    | TyVar { contents = Link _ } -> failwith "unexpected: Link"
    | TyVar { contents = Unbound(id, NoRow, _) } -> id
    | TyVar { contents = Unbound(id, (OpenRow _ as row), _) } ->
      id ^ print_row ty_pretty row
    | TyVar { contents = Unbound(_, (ClosedRow _ as row), _) } ->
      print_row ty_pretty row
    | TyArrow (from, dst) ->
      ty_pretty from ^ " -> " ^ ty_pretty dst
    | TyName name -> name
    | TyApp app -> String.concat ~sep:" " (List.map app ~f:ty_pretty)

  let rec ty_debug ty =
    match ty with
    | TyBool -> "TyBool"
    | TyVar { contents = Link ty } ->
      Printf.sprintf "TyVar(Link(%s))" (ty_debug ty)
    | TyVar { contents = Unbound(id, NoRow, scope) } ->
      Printf.sprintf "TyVar(Unbound(%s,%d))" id scope
    | TyVar { contents = Unbound(id, ((OpenRow _ | ClosedRow _) as row), scope) } ->
      Printf.sprintf "TyVar(Unbound(%s, %s, %d))" id (print_row ty_debug row) scope
    | TyArrow(from, dst) ->
      "(" ^ ty_debug from ^ " -> " ^ ty_debug dst ^ ")"
    | TyName name -> name
    | TyApp app -> String.concat ~sep:" " (List.map app ~f:ty_debug)

  exception Undefined of string
  exception UnificationFailure of string
  exception OccursCheck
  exception TypeError of string
  exception Expected of string
  exception RowMismatch of string
  exception UnboundTypeVar of string

  let unbound_typevar id =
    UnboundTypeVar (Printf.sprintf "unresolved type variable %s after typechecking" id)

  let undefined_error kind name =
    Undefined (Printf.sprintf "%s %s not defined" kind name)

  let unify_failed t1 t2 =
    UnificationFailure
      (Printf.sprintf "failed to unify type %s with %s" (ty_pretty t1) (ty_pretty t2))

  let type_error ty =
    TypeError(Printf.sprintf "expression does not have type %s" (ty_pretty ty))

  let expected_ty_error expected got =
    Expected (Printf.sprintf "expected type %s, got %s" expected got)

  let row_mismatch row1 row2 =
    RowMismatch (Printf.sprintf "%s and %s" (print_row ty_pretty row1) (print_row ty_pretty row2))

  let cannot_apply name =
    UnificationFailure (Printf.sprintf "cannot apply %s" name)

  (* Lookup a variable's type in the environment. *)
  let lookup_var_type name (e : env) : generic_ty =
    match List.Assoc.find e ~equal name with
    | Some (VarBind t) -> t
    | _ -> raise (undefined_error "variable" name)

  let lookup_binding name (e : env) : bind =
    match List.Assoc.find e ~equal name with
    | Some b -> b
    | None -> raise (undefined_error "type" name)

  let rec wf_ty (env : env) (ty : ty) : unit =
    match ty with
    | TyBool -> ()
    | TyArrow (from, dst) -> wf_ty env from; wf_ty env dst
    | TyName name -> ignore (lookup_binding name env)
    | TyApp tys -> List.iter tys ~f:(wf_ty env)
    | TyVar _ -> ()

  let wf_tycon (env : env) (tc : tycon) : unit =
    let env =
      List.map tc.type_params ~f:(fun p -> (p, TypeVarBind NoRow)) @ env
    in
    List.iter tc.ty ~f:(fun (_, ty) -> wf_ty env ty)

  (* Get the type of a typed expression. *)
  let typ (texp : texp) : ty =
    match texp with
    | TEBool _ -> TyBool
    | TEVar (_, ty) -> ty
    | TEApp (_, _, ty) -> ty
    | TELam (_, _, ty) -> ty
    | TEIf (_, _, _, ty) -> ty
    | TERecord (_, ty) -> ty
    | TEWith (_, _, ty) -> ty
    | TEProj (_, _, ty) -> ty
    | TELet (_, _, ty) -> ty
    | TELetRec (_, _, ty) -> ty

  (* Global state that stores a counter for generating fresh unbound type variables. *)
  let gensym_counter = ref 0
  (* Global state that stores the current scope. *)
  let current_scope = ref 1
  let enter_scope () = Int.incr current_scope
  let leave_scope () = Int.decr current_scope

  (* Generate a fresh unbound type variable with a unique name, an optional
    row constraint, and the current scope. *)
  let fresh_unbound_var ?(row=NoRow) () =
    let n = !gensym_counter in
    Int.incr gensym_counter;
    let tvar = "?" ^ Int.to_string n in
    TyVar (ref (Unbound (tvar, row, !current_scope)))

  let row_iter (row: row_constraint) f =
    match row with
    | NoRow -> ()
    | OpenRow flds | ClosedRow flds -> List.iter flds ~f

  let map_row ~f row =
    match row with
    | NoRow -> NoRow
    | OpenRow flds -> OpenRow (List.map flds ~f:(fun (id, ty) -> (id, f ty)))
    | ClosedRow flds -> ClosedRow (List.map flds ~f:(fun (id, ty) -> (id, f ty)))

  let apply_tyapp env (ty : ty) : record_ty =
    let substitute (tbl : (id, ty) Hashtbl.t) (ty : ty) : ty =
      let rec sub ty =
        match force ty with
        | TyName id as ty ->
          (match Hashtbl.find tbl id with
           | Some t -> t
           | None -> ty)
        | TyArrow (from, dst) -> TyArrow (sub from, sub dst)
        | TyApp app -> TyApp (List.map app ~f:sub)
        | ty -> ty
      in sub ty
    in
    match force ty with
    | TyName name ->
      (match lookup_binding name env with
       | TypeBind tc when List.is_empty tc.type_params -> tc.ty
       | TypeBind _ -> raise (cannot_apply name)
       | TypeVarBind _ | VarBind _ -> raise (undefined_error "type" name))
    | TyApp (TyName name :: args) ->
      (match lookup_binding name env with
       | TypeBind tc ->
         (match List.zip tc.type_params args with
          | Ok pairs ->
            let tbl = Hashtbl.of_alist_exn (module String) pairs in
            List.map tc.ty ~f:(fun (id, t) -> (id, substitute tbl t))
          | Unequal_lengths -> raise (cannot_apply name))
       | TypeVarBind _ | VarBind _ -> raise (undefined_error "type" name))
    | _ -> failwith "apply_tyapp: expected TyName or TyApp"

  let rec union_rows env (row_a: row_constraint) (row_b: row_constraint) : row_constraint =
    match (row_a, row_b) with
    | NoRow, row | row, NoRow -> row
    | OpenRow row_a, OpenRow row_b ->
      OpenRow (List.dedup_and_sort (row_a @ row_b) ~compare:(fun (f1,t1) (f2,t2) ->
        if String.equal f1 f2 then (unify env t1 t2; 0)
        else Poly.compare (f1,t1) (f2,t2)))
    | OpenRow o_row, ClosedRow c_row | ClosedRow c_row, OpenRow o_row ->
      List.iter o_row ~f:(fun (id,ty) ->
        if not (fld_exists env c_row id ty) then
          raise (row_mismatch row_a row_b)); ClosedRow c_row
    | ClosedRow flds1, ClosedRow flds2 when Int.equal (List.length flds1) (List.length flds2) ->
      List.iter flds1 ~f:(fun (id,ty) ->
        if not (fld_exists env flds2 id ty) then
          raise (row_mismatch row_a row_b)); ClosedRow flds1
    | _ -> raise (row_mismatch row_a row_b)

  and fld_exists env (rcd: record_ty) id ty =
    List.exists rcd ~f:(fun (f,t) -> String.equal f id && (unify env t ty; true))

  (* Occurs check: check if a type variable occurs in a type. If it does, raise
    an exception. *)
  and occurs (src : tv ref) (ty : ty) : unit =
    (* Follow all the links. If we see a type variable, it will only be
       Unbound. *)
    match force ty with
    | TyVar tgt when phys_equal src tgt ->
      (* src type variable occurs in ty. *)
      raise OccursCheck
    | TyVar ({ contents = Unbound (id, tgt_row, tgt_scope) } as tgt) ->
      row_iter tgt_row (fun (_, ty) -> occurs src ty);
      (* Grabbed src and tgt's scopes. *)
      let { contents = Unbound(_, _, src_scope) } = src in
      (* Compute the minimum of their scopes (the outermost scope). *)
      let min_scope = min src_scope tgt_scope in
      (* Update the tgt's scope to be the minimum. *)
      tgt := Unbound (id, tgt_row, min_scope)
    | TyArrow(from, dst) ->
      (* Check that src occurs in the arrow type. *)
      occurs src from;
      occurs src dst;
    | TyApp app -> List.iter app ~f:(occurs src)
    | _ -> ()

  (* Check that tv_row's fields are contained within rigid_row. *)
  and check_rigid_subset env tname tv_row rigid_row =
    match tv_row, rigid_row with
    | NoRow, _ -> ()
    | _, NoRow -> raise (expected_ty_error "record" tname)
    | OpenRow flds, OpenRow rigid_flds
    | OpenRow flds, ClosedRow rigid_flds ->
      List.iter flds ~f:(fun (id, ty) ->
        if not (fld_exists env rigid_flds id ty) then
          raise (row_mismatch tv_row rigid_row))
    | _ -> raise (row_mismatch tv_row rigid_row)

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
      let Unbound(_, tv_row, src_scope) = !tv in
      (match ty with
      | TyName tname ->
        (match lookup_binding tname env with
         | TypeVarBind rigid_row -> check_rigid_subset env tname tv_row rigid_row
         | VarBind _ -> raise (undefined_error "type" tname)
         | TypeBind _ ->
           let tycon_row = ClosedRow (apply_tyapp env ty) in
           ignore (union_rows env tv_row tycon_row))
      | TyApp _ ->
        let tycon_row = ClosedRow (apply_tyapp env ty) in
        ignore (union_rows env tv_row tycon_row)
      | TyVar other when not (phys_equal tv other) ->
        (* Union the rows of these two distinct type variables, and lower
          the surviving tvar's scope to the minimum. *)
        let Unbound(id, other_row, other_scope) = !other in
        row_iter other_row (fun (_, ty) -> occurs tv ty);
        let min_scope = min src_scope other_scope in
        let row = union_rows env tv_row other_row in
        other := Unbound(id, row, min_scope)
      | _ when equal tv_row NoRow ->
        (* If either type is a type variable, ensure that the type variable
          does not occur in the type. occurs also lowers scopes. *)
        occurs tv ty
      | _ ->
        (* ty is not record-like. Can't unify with a row. *)
        raise (unify_failed t1 t2));
      (* Link the type variable to the type. *)
      tv := Link ty
    | TyName a, TyName b when equal a b -> () (* The type names are the same. *)
    | TyApp app1, TyApp app2 when List.length app1 = List.length app2 ->
      List.iter2_exn app1 app2 ~f:(unify env)
    | _ ->
      (* Unification has failed. *)
      raise (unify_failed t1 t2)

  (* The environment stores generic types, but sometimes we need to associate
    a non-generalized type to a variable. This function wraps a type into a
    trivial generic type (no quantified parameters). *)
  let dont_generalize ty : generic_ty = { type_params = []; ty }

  let gen (ty: ty) : generic_ty =
    let type_params : (id, row_constraint) Hashtbl.t = Hashtbl.create (module String) in
    let rec gen' ty =
      match force ty with
      | TyVar ({ contents = Unbound (id, row, scope) } as tv) when scope > !current_scope ->
        Hashtbl.set type_params ~key:id ~data:(map_row ~f:gen' row);
        (* Mutate the tvar to Link to its generalized TyName, so the
          post-pass walking the AST doesn't see it as Unbound. *)
        tv := Link (TyName id);
        TyName id
      | TyArrow (from, dst) -> TyArrow (gen' from, gen' dst)
      | TyApp app -> TyApp (List.map app ~f:gen')
      | ty -> ty
    in
    let ty = gen' ty in
    let type_params =
      Hashtbl.to_alist type_params
      |> List.sort ~compare:(fun (a,_) (b,_) -> String.compare a b)
    in
    { type_params; ty }

  (* Instantiate a generic type by replacing all the type parameters
   with fresh unbound type variables. Ensure that the same ID gets
   mapped to the same unbound type variable by using an (id, ty) Hashtbl. *)
  let inst (gty: generic_ty) : ty =
    let tbl = Hashtbl.create (module String) in
    List.iter gty.type_params ~f:(fun (pid, _) ->
      Hashtbl.set tbl ~key:pid ~data:(fresh_unbound_var ()));
    let rec inst' ty =
      match force ty with
      | TyName id as ty -> (
        match Hashtbl.find tbl id with
        | Some tv -> tv
        | None -> ty)
      | TyArrow (from, dst) -> TyArrow (inst' from, inst' dst)
      | TyApp app -> TyApp (List.map app ~f:inst')
      | ty -> ty
    in
    (* Attach the instantiated row constraint to each fresh type variable in the table. *)
    List.iter gty.type_params ~f:(fun (pid, row) ->
      match row with
      | NoRow -> ()
      | _ ->
        let TyVar tv = Hashtbl.find_exn tbl pid in
        let Unbound(id, _, scope) = !tv in
        tv := Unbound(id, map_row ~f:inst' row, scope));
    inst' gty.ty

  (* Turn a generic_ty into its rigid form, so that when annotations are instantiated,
     they don't produce Unbound type variables that can unify with each other.*)
  let as_rigid (gty: generic_ty) : env * ty =
    let extras = List.map gty.type_params ~f:(fun (id, row) -> (id, TypeVarBind row)) in
    (extras, gty.ty)

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
      (* instantiate its type by replacing all of its quantified type
         variables with fresh unbound type variables. *)
      TEVar (name, inst var_ty)
    | ELam (param, body) ->
      (* Instantiate a fresh type variable for the lambda parameter, and
          extend the environment with the param and its type. *)
      let ty_param = fresh_unbound_var () in
      let env' = (param, VarBind (dont_generalize ty_param)) :: env in
      (* Typecheck the body of the lambda with the extended environment. *)
      let body = infer env' body in
      (* Return a synthesized arrow type from the parameter to the body. *)
      TELam (param, body, TyArrow (ty_param, typ body))
    | EApp (fn, arg) ->
      (* To typecheck a function application, first infer the types of the
          function and the argument. *)
      let fn = infer env fn in
      let arg = infer env arg in
      (* Instantiate a fresh type variable for the result of the application,
          and synthesize an arrow type going from the argument to the
          result. *)
      let ty_res = fresh_unbound_var () in
      let ty_arr = TyArrow (typ arg, ty_res) in
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
      (* Return the type of one of the branches. (we'll pick the "then" branch) *)
      TEIf (cond, thn, els, typ thn)
    | ERecord rec_lit ->
      let rec_lit = List.map rec_lit ~f:(fun (id, x) -> (id, infer env x)) in
      let flds = List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit in
      TERecord (rec_lit, fresh_unbound_var ~row:(ClosedRow flds) ())
    | EWith (rcd, flds) ->
      let rcd = infer env rcd in
      let rec_lit = List.map flds ~f:(fun (id, x) -> (id, infer env x)) in
      let flds = List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit in
      let row = fresh_unbound_var ~row:(OpenRow flds) () in
      unify env (typ rcd) row;
      TEWith (rcd, rec_lit, typ rcd)
    | EProj (rcd, fld) ->
      let rcd = infer env rcd in
      let fld_ty = fresh_unbound_var () in
      let row = fresh_unbound_var ~row:(OpenRow [(fld, fld_ty)]) () in
      unify env (typ rcd) row;
      TEProj (rcd, fld, fld_ty)
    | ELet ((id, ann, rhs), body) ->
      enter_scope();
      let rhs =
        match ann with
        | Some ann ->
          let (extras, check_ty) = as_rigid ann in
          check (extras @ env) check_ty rhs
        | None -> infer env rhs
      in
      leave_scope();
      let ty_gen =
        match ann with
        | Some ann -> ann
        | None -> gen (typ rhs)
      in
      let env_body = (id, VarBind ty_gen) :: env in
      let body = infer env_body body in
      TELet ((id, ann, rhs), body, typ body)
    | ELetRec (decls, body) ->
      enter_scope();
      let prepared = List.map decls ~f:(fun (id, ann, rhs) ->
        match ann with
        | Some ann ->
          let (extras, check_ty) = as_rigid ann in
          (id, Some ann, rhs, extras, check_ty)
        | None ->
          (id, None, rhs, [], fresh_unbound_var ()))
      in
      let env_decls = List.map prepared ~f:(fun (id, _, _, _, check_ty) ->
        (id, VarBind (dont_generalize check_ty)))
      in
      let env_with_decls = env_decls @ env in
      let tdecls : tlet_decl list = List.map prepared ~f:(fun (id, ann, rhs, extras, check_ty) ->
        let trhs = check (extras @ env_with_decls) check_ty rhs in
        (id, ann, trhs))
      in
      leave_scope();
      let generalized_bindings = List.map tdecls ~f:(fun (id, ann, rhs) ->
        let ty_gen =
          match ann with
          | Some ann -> ann
          | None -> gen (typ rhs)
        in
        (id, VarBind ty_gen))
      in
      let env_body = generalized_bindings @ env in
      let body = infer env_body body in
      TELetRec (tdecls, body, typ body)

  (* Walk the typed AST to check for any Unbound type variables, and if found, raise an exception. *)
  let check_no_unbound (texp : texp) : unit =
    let rec ck_ty (ty : ty) : unit =
      match force ty with
      | TyVar { contents = Unbound (id, _, _) } -> raise (unbound_typevar id)
      | TyVar { contents = Link _ } -> failwith "unexpected: Link after force"
      | TyArrow (from, dst) -> ck_ty from; ck_ty dst
      | TyApp app -> List.iter app ~f:ck_ty
      | TyBool | TyName _ -> ()
    in
    let rec walk (texp : texp) =
      ck_ty (typ texp);
      match texp with
      | TEBool _ | TEVar _ -> ()
      | TELam (_, body, _) -> walk body
      | TEApp (fn, arg, _) -> walk fn; walk arg
      | TEIf (cond, thn, els, _) -> walk cond; walk thn; walk els
      | TERecord (rec_lit, _) -> List.iter rec_lit ~f:(fun (_, x) -> walk x)
      | TEWith (rcd, rec_lit, _) ->
        walk rcd; List.iter rec_lit ~f:(fun (_, x) -> walk x)
      | TEProj (rcd, _, _) -> walk rcd
      | TELet ((_, _, rhs), body, _) -> walk rhs; walk body
      | TELetRec (decls, body, _) ->
        List.iter decls ~f:(fun (_, _, rhs) -> walk rhs);
        walk body
    in
    walk texp

  let typecheck_prog ((tl, exp): prog) : texp =
    let env = List.map tl ~f:(fun tc -> (tc.name, TypeBind tc)) in
    List.iter tl ~f:(wf_tycon env);
    let texp = infer env exp in
    check_no_unbound texp;
    texp

  let convert_prog (ast_prog : Ast.prog) : prog =
    Ast.map_prog
      ~on_ty_bool:(fun () -> TyBool)
      ~on_ty_arrow:(fun a b -> TyArrow (a, b))
      ~on_ty_name:(fun x -> TyName x)
      ~on_ty_app:(fun ts -> TyApp ts)
      ~on_no_row:(fun () -> NoRow)
      ~on_open_row:(fun flds -> OpenRow flds)
      ~on_closed_row:(fun flds -> ClosedRow flds)
      ~on_generic_ty:(fun ps ty -> { type_params = ps; ty })
      ~on_tycon:(fun name type_params ty -> { name; type_params; ty })
      ~on_let_decl:(fun id ann rhs -> (id, ann, rhs))
      ~on_bool:(fun b -> EBool b)
      ~on_var:(fun x -> EVar x)
      ~on_lam:(fun x body -> ELam (x, body))
      ~on_app:(fun f a -> EApp (f, a))
      ~on_if:(fun c t e -> EIf (c, t, e))
      ~on_record:(fun lit -> ERecord lit)
      ~on_with:(fun rcd lit -> EWith (rcd, lit))
      ~on_proj:(fun rcd fld -> EProj (rcd, fld))
      ~on_let:(fun d body -> ELet (d, body))
      ~on_letrec:(fun ds body -> ELetRec (ds, body))
      ~on_prog:(fun tycons e -> (tycons, e))
      ast_prog

  let typecheck_source src =
    src |> Parser.parse_string |> convert_prog |> typecheck_prog

  let expect_type ty src =
    Poly.equal (ty_pretty (typ (typecheck_source src))) ty

  let expect_raises exn src =
    try ignore (typecheck_source src); false
    with e -> equal e exn
end

let%test "basic" =
  let open Eight() in
  expect_type "bool" "(fun x -> x) true"

let%test "basic_error" =
  let open Eight() in
  expect_raises
    (UnificationFailure "failed to unify type bool -> ?1 with bool")
    "(fun f -> f true) true"

let%test "if" =
  let open Eight() in
  expect_type "bool" "if true then false else (fun x -> x) true"

let%test "if_error" =
  let open Eight() in
  expect_raises
    (UnificationFailure "failed to unify type bool with ?0 -> ?0")
    "if true then false else fun x -> x"

let%test "let" =
  let open Eight() in
  expect_type "bool" "let x = true in if x then false else true"

let%test "let_ann" =
  let open Eight() in
  expect_raises
    (TypeError "expression does not have type bool")
    "let x : bool = fun y -> y in x"

let%test "let_rec" =
  let open Eight() in
  expect_type "bool" {|
    let rec f = fun x -> if x then g x else x
    and g = fun x -> if x then f x else x in
    f true
  |}

let%test "let_rec_error" =
  let open Eight() in
  expect_raises
    (UnificationFailure "failed to unify type bool -> bool with bool")
    {|
      let rec f = fun x -> if x then g x else x
      and g : bool -> bool -> bool = fun x -> if x then f x else x in
      f true
    |}

let%test "tycon_undefined" =
  let open Eight() in
  expect_raises
    (Undefined "type Bogus not defined")
    {|
      type Foo = { x : Bogus }
      true
    |}

let%test "record_via_unparameterized_tycon" =
  let open Eight() in
  expect_type "bool" {|
    type Foo = { x : bool, y : bool -> bool }
    let foo : Foo = { x = true, y = fun x -> x } in foo.y true
  |}

let%test "row" =
  let open Eight() in
  expect_type "bool" {|
    type Foo = { y : bool -> bool }
    let r : Foo = { y = fun x -> x } in (fun s -> s.y) r true
  |}

let%test "row2" =
  let open Eight() in
  expect_type "bool" {|
    type Foo = { f : bool -> bool }
    type Bar = { x : bool }
    let r1 : Bar = { x = true } in
    let r2 : Foo = { f = fun x -> x } in
    (fun a -> fun b -> b.f a.x) r1 r2
  |}

let%test "row_if" =
  let open Eight() in
  expect_raises
    (UnificationFailure "failed to unify type Foo with Bar")
    {|
      type Foo = { x : bool }
      type Bar = { x : bool, y : bool }
      let foo : Foo = { x = true } in
      let bar : Bar = { x = true, y = true } in
      if true then foo else bar
    |}

let%test "row_with" =
  let open Eight() in
  expect_raises
    (RowMismatch "{y: bool, ...} and {x: bool}")
    {|
      type Foo = { x : bool }
      let foo : Foo = { x = true } in { foo with y = true }
    |}

let%test "let_gen" =
  let open Eight() in
  expect_type "bool" {|
    type A = {}
    let a : A = {} in
    let f = fun x -> x in
    let _ = f a in
    f true
  |}

let%test "fix" =
  let open Eight() in
  expect_type "bool -> bool" {|
    let rec fix = fun f -> fun x -> f (fix f) x in
    fix (fun f -> fun arg -> if arg then f false else true)
  |}

let%test "let_gen_ann" =
  let open Eight() in
  expect_type "bool" {|
    type A = {}
    let a : A = {} in
    let f : forall 'a. 'a -> bool = fun x -> true in
    f a
  |}

let%test "let_gen_error" =
  let open Eight() in
  expect_raises
    (TypeError "expression does not have type 'a -> A")
    {|
      type A = {}
      let f : forall 'a. 'a -> A = fun x -> true in
      f true
    |}

let%test "let_gen_scope_error" =
  let open Eight() in
  expect_raises
    (UnificationFailure "failed to unify type bool with bool -> ?2")
    "(fun x -> let y = x in y) true true"

let%test "let_typevar_ref" =
  let open Eight() in
  expect_type "bool" {|
    let f : forall 'a. 'a -> 'a = fun x -> let y : 'a = x in y in
    f true
  |}

let%test "let_rec_typevar_ref" =
  let open Eight() in
  expect_type "bool" {|
    let rec f : forall 'a. 'a -> 'a = fun x -> let y : 'a = x in y in
    f true
  |}

let%test "let_rigid_ok" =
  let open Eight() in
  expect_type "bool" {|
    let f : forall 'a. 'a -> 'a = fun x -> x in
    f true
  |}

let%test "let_rigid_error" =
  let open Eight() in
  expect_raises
    (TypeError "expression does not have type 'a -> 'b")
    "let f : forall 'a 'b. 'a -> 'b = fun x -> x in f"

let%test "let_rec_rigid_error" =
  let open Eight() in
  expect_raises
    (TypeError "expression does not have type 'a -> 'b")
    "let rec f : forall 'a 'b. 'a -> 'b = fun x -> x in f"

let%test "row_ann" =
  let open Eight() in
  expect_type "bool" {|
    type Foo = { x : bool, y : bool }
    let get_x : forall 'r. 'r :: { x : bool, ... } => 'r -> bool =
      fun r -> r.x
    in
    let foo : Foo = { x = true, y = false } in
    get_x foo
  |}

let%test "row_ann_missing_field" =
  let open Eight() in
  expect_raises
    (RowMismatch "{x: bool, ...} and {y: bool}")
    {|
      type Foo = { y : bool }
      let get_x : forall 'r. 'r :: { x : bool, ... } => 'r -> bool =
        fun r -> r.x
      in
      let foo : Foo = { y = true } in
      get_x foo
    |}

let%test "ann_missing_row_constraint" =
  let open Eight() in
  expect_raises
    (Expected "expected type record, got 'a")
    "let f : forall 'a. 'a -> bool = fun r -> r.x in true"

let%test "let_gen_row" =
  let open Eight() in
  expect_type "bool -> bool" {|
    type Foo = { x : bool }
    type Bar = { x : bool -> bool }
    let r1 : Foo = { x = true } in
    let r2 : Bar = { x = fun y -> y } in
    let f = fun r -> r.x in
    let _ = f r1 in
    f r2
  |}

let%test "generic_tycon" =
  let open Eight() in
  expect_type "bool" {|
    type box 'a = { x : 'a }
    let r : box bool = { x = true } in r.x
  |}

let%test "generic_tycon_let_gen" =
  let open Eight() in
  expect_type "box bool" {|
    type box 'a = { x : 'a }
    let identity : forall 'a. box 'a -> box 'a = fun b -> b in
    identity (let r : box bool = { x = true } in r)
  |}

let%test "generic_tycon_error" =
  let open Eight() in
  expect_raises
    (RowMismatch "{x: bool} and {x: bool, y: bool}")
    {|
      type box 'a = { x : 'a, y : bool }
      let r : box bool = { x = true } in r.x
    |}
