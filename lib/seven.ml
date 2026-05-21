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
    | TyName of id (* Type name: Foo *)
  and record_ty = (id * ty) list
  (* A row constraint sits on an unbound type variable. It records what
    record-shape the variable must have. *)
  and row_constraint =
    | NoRow (* No row constraint. *)
    | OpenRow of record_ty (* Must contain at least these fields (from EProj/EWith). *)
    | ClosedRow of record_ty (* Must contain exactly these fields (from ERecord). *)
  and tv = (* A type variable *)
    | Unbound of id * row_constraint * scope
      (* Unbound type variable: Holds the type variable's unique name, any
        row constraint, and the scope at which it was created. *)
    | Link of ty (* Link type variable: Holds a reference to a type. *)
  (* Type declaration/constructor. All type declarations are nominal records. *)
  type tycon = {
    name : id;
    ty : record_ty;
  }
  (* A generic type. Should be read as forall p1::r1..pn::rn. ty, where each
    pi is a type parameter and ri its row constraint (NoRow for plain
    parameters). The forall is only allowed at the top level of a type,
    matching standard HM. *)
  type generic_ty = {
    type_params : (id * row_constraint) list;
    ty : ty;
  }
  type bind =
    | VarBind of generic_ty (* A variable binding maps to a generic type. *)
    | TypeBind of tycon (* A type binding maps to a type constructor. *)
    | TypeVarBind of row_constraint
      (* A rigid type-variable binding. Introduced when entering the RHS of
        an annotated let: each declared type parameter becomes a rigid
        `TyName "'a"` whose only structural information lives here, as the
        row constraint it must satisfy. The binding's *name* is the rigid
        name; operations on `TyName "'a"` consult `lookup_typevar` before
        falling back to `lookup_tycon`. *)
  type env = (id * bind) list
  type exp =
    | EBool of bool (* true/false *)
    | EVar of id (* x *)
    | ELam of id * exp (* fun x -> x *)
    | EApp of exp * exp (* f arg *)
    | EIf of exp * exp * exp (* if <exp> then <exp> else <exp> *)
    | ERecord of record_lit (* {x = true, y = false} *)
    | EWith of exp * record_lit (* { r with x = true, y = false } *)
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
    | TyVar { contents = Unbound(id, NoRow, _) } -> id
    | TyVar { contents = Unbound(id, OpenRow flds, _) } ->
      Printf.sprintf "%s{%s}" id (ty_fields ty_pretty flds)
    | TyVar { contents = Unbound(_, ClosedRow flds, _) } ->
      Printf.sprintf "{%s}" (ty_fields ty_pretty flds)
    | TyArrow (from, dst) ->
      ty_pretty from ^ " -> " ^ ty_pretty dst
    | TyName name -> name

  let rec ty_debug ty =
    match ty with
    | TyBool -> "TyBool"
    | TyVar { contents = Link ty } ->
      Printf.sprintf "TyVar(Link(%s))" (ty_debug ty)
    | TyVar { contents = Unbound(id, NoRow, scope) } ->
      Printf.sprintf "TyVar(Unbound(%s,%d))" id scope
    | TyVar { contents = Unbound(id, OpenRow flds, scope) } ->
      Printf.sprintf "TyVar(Unbound(%s, OpenRow{%s}, %d))" id (ty_fields ty_debug flds) scope
    | TyVar { contents = Unbound(id, ClosedRow flds, scope) } ->
      Printf.sprintf "TyVar(Unbound(%s, ClosedRow{%s}, %d))" id (ty_fields ty_debug flds) scope
    | TyArrow(from, dst) ->
      "(" ^ ty_debug from ^ " -> " ^ ty_debug dst ^ ")"
    | TyName name -> name

  let print_row f row =
    match row with
    | NoRow -> "NoRow"
    | OpenRow flds -> Printf.sprintf "OpenRow{%s}" (ty_fields f flds)
    | ClosedRow flds -> Printf.sprintf "ClosedRow{%s}" (ty_fields f flds)


  exception Undefined of string
  exception DuplicateDefinition of string
  exception MissingField of string
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

  let duplicate_definition def =
    DuplicateDefinition (Printf.sprintf "duplicate definition of %s" def)

  let unify_failed t1 t2 =
    UnificationFailure
      (Printf.sprintf "failed to unify type %s with %s" (ty_pretty t1) (ty_pretty t2))

  let missing_field field inside =
    MissingField (Printf.sprintf "missing field %s in %s" field inside)

  let type_error ty =
    TypeError(Printf.sprintf "expression does not have type %s" (ty_pretty ty))

  let expected_ty_error expected got =
    Expected (Printf.sprintf "expected type %s, got %s" expected got)

  let row_mismatch row1 row2 =
    RowMismatch (Printf.sprintf "%s and %s" (print_row ty_pretty row1) (print_row ty_pretty row2))

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

  (* Lookup a type-variable binding by name. Returns the row constraint
    the rigid satisfies, or None if the name is not in scope as a type
    variable (the caller falls back to tycon lookup). *)
  let lookup_typevar name (e : env) : row_constraint option =
    match List.Assoc.find e ~equal name with
    | Some (TypeVarBind r) -> Some r
    | _ -> None

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

  (* Union two row constraints from a single unbound type variable's
    perspective. Open rows merge by collecting fields and unifying any
    overlap. An open row unified with a closed row must be a subset of
    the closed row (the result is closed). Closed-with-closed requires
    exact-set equality. Otherwise the rows are incompatible. *)
  let rec union_rows env (row_a: row_constraint) (row_b: row_constraint) : row_constraint =
    match (row_a, row_b) with
    | NoRow, row | row, NoRow -> row
    | OpenRow row_a, OpenRow row_b ->
      OpenRow (List.dedup_and_sort (row_a @ row_b) ~compare:(fun (f1,t1) (f2,t2) ->
        if f1 = f2 then (unify env t1 t2; 0)
        else Poly.compare (f1,t1) (f2,t2)))
    | OpenRow o_row, ClosedRow c_row | ClosedRow c_row, OpenRow o_row ->
      List.iter o_row (fun (id,ty) ->
        if not (fld_exists env c_row id ty) then
          raise (row_mismatch row_a row_b)); ClosedRow c_row
    | ClosedRow flds1, ClosedRow flds2 when Int.equal (List.length flds1) (List.length flds2) ->
      List.iter flds1 (fun (id,ty) ->
        if not (fld_exists env flds2 id ty) then
          raise (row_mismatch row_a row_b)); ClosedRow flds1
    | _ -> raise (row_mismatch row_a row_b)

  and fld_exists env (rcd: record_ty) id ty =
    List.exists rcd ~f:(fun (f,t) -> String.equal f id && (unify env t ty; true))

  (* Occurs check: check if a type variable occurs in a type. If it does,
    raise an exception. While walking the type we also lower the scope of
    any unbound tvar we visit to the minimum of src's and its own scope —
    this is what keeps generalization sound when a tvar from a deeper scope
    is unified into a shallower one. *)
  and occurs (src : tv ref) (ty : ty) : unit =
    (* Follow all the links. If we see a type variable, it will only be
       Unbound. *)
    match force ty with
    | TyVar tgt when src == tgt ->
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
    | _ -> ()

  (* Check that a tvar's accumulated row constraint is satisfied by a
    rigid's row. Rigid rows are opaque — they may not be widened — so the
    rule is strict subset: every field tv requires must appear (and unify)
    in the rigid's row. A `ClosedRow` on the tvar means the tvar IS a
    specific record type, which can't masquerade as an opaque rigid. *)
  and check_rigid_subset env tv_row rigid_row =
    match tv_row, rigid_row with
    | NoRow, _ -> ()
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
        (* `TyName "X"` can be either a rigid (an annotation's type
          parameter currently in scope) or a nominal tycon. Try the rigid
          path first: a rigid allows the tvar's row to be a subset, but
          never widens it. If the name isn't a rigid, fall back to the
          tycon path, treating the tycon's fields as a closed row. *)
        (match lookup_typevar tname env with
         | Some rigid_row ->
           check_rigid_subset env tv_row rigid_row
         | None ->
           let tc = lookup_tycon tname env in
           ignore (union_rows env tv_row (ClosedRow tc.ty)))
      | TyVar other when tv != other ->
        (* Union the rows of these two distinct type variables, and lower
          the surviving tvar's scope to the minimum. *)
        let Unbound(id, other_row, other_scope) = !other in
        row_iter other_row (fun (_, ty) -> occurs tv ty);
        let min_scope = min src_scope other_scope in
        let row = union_rows env tv_row other_row in
        other := Unbound(id, row, min_scope)
      | _ when not (equal tv_row NoRow) ->
        (* The tvar carries a row constraint but the other side is not a
          record-like type — no possible unification. *)
        raise (unify_failed t1 t2)
      | _ ->
        (* If either type is a type variable, ensure that the type variable
          does not occur in the type. occurs also lowers scopes. *)
        occurs tv ty);
      (* Link the type variable to the type. *)
      tv := Link ty
    | TyName a, TyName b when equal a b -> () (* The type names are the same. *)
    | _ ->
      (* Unification has failed. *)
      raise (unify_failed t1 t2)

  (* The environment stores generic types, but sometimes we need to associate
    a non-generalized type to a variable. This function wraps a type into a
    trivial generic type (no quantified parameters). *)
  let dont_generalize ty : generic_ty = { type_params = []; ty }

  (* Generalize a type by finding every unbound tvar whose scope is strictly
    deeper than the current scope and turning it into a quantified type
    parameter. Row constraints on those tvars become row constraints on the
    corresponding parameter; field types inside those rows are themselves
    recursively generalized, so e.g. `?r{value: ?v}` becomes a generic with
    `?r::{value: ?v, ...}, ?v::NoRow` as the parameters. *)
  let gen (ty: ty) : generic_ty =
    let type_params : (id, row_constraint) Hashtbl.t = Hashtbl.create (module String) in
    let rec gen' ty =
      match force ty with
      | TyVar ({ contents = Unbound (id, row, scope) } as tv) when scope > !current_scope ->
        Hashtbl.set type_params ~key:id ~data:(gen_row row);
        (* Mutate the tvar to Link to its generalized TyName, so the
          post-pass walking the AST doesn't flag it as still-unresolved. *)
        tv := Link (TyName id);
        TyName id
      | TyArrow (from, dst) -> TyArrow (gen' from, gen' dst)
      | ty -> ty
    and gen_row row =
      match row with
      | NoRow -> NoRow
      | OpenRow flds -> OpenRow (List.map flds ~f:(fun (id, ty) -> (id, gen' ty)))
      | ClosedRow flds -> ClosedRow (List.map flds ~f:(fun (id, ty) -> (id, gen' ty)))
    in
    let ty = gen' ty in
    let type_params =
      Hashtbl.to_alist type_params
      |> List.sort ~compare:(fun (a,_) (b,_) -> String.compare a b)
    in
    { type_params; ty }

  (* Instantiate a generic type by replacing each type parameter with a
    fresh unbound tvar. Field types inside row constraints are substituted
    through the same parameter->tvar map, so e.g. `forall a::{x: b, ...}, b.
    a -> b` becomes `?n1{x: ?n2, ...} -> ?n2` with both occurrences of `b`
    pointing at the same fresh tvar. *)
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
      | ty -> ty
    in
    let inst_row row =
      match row with
      | NoRow -> NoRow
      | OpenRow flds -> OpenRow (List.map flds ~f:(fun (id, ty) -> (id, inst' ty)))
      | ClosedRow flds -> ClosedRow (List.map flds ~f:(fun (id, ty) -> (id, inst' ty)))
    in
    (* Now attach the (instantiated) row constraint to each fresh tvar.
      We do this after the table is fully populated so rows that reference
      other parameters resolve correctly. *)
    List.iter gty.type_params ~f:(fun (pid, row) ->
      match row with
      | NoRow -> ()
      | _ ->
        match Hashtbl.find_exn tbl pid with
        | TyVar tv ->
          let Unbound(id, _, scope) = !tv in
          tv := Unbound(id, inst_row row, scope)
        | _ -> failwith "unreachable: tbl always holds TyVars");
    inst' gty.ty

  (* Turn a generic_ty into its rigid form for *checking* an annotated
    let's RHS. Each type parameter `'a` becomes a rigid `TyName "'a"` whose
    row constraint lives in the environment as a `TypeVarBind`. The body
    of the generic is returned untouched — its `TyName "'a"` references
    are already the rigid names, and any nested annotation that mentions
    `'a` will resolve through the env. Compare with [inst], which is used
    at *use* sites and creates fresh tvars per use. *)
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
      (* A record literal has a closed row: its set of fields is exactly the
        ones written. We still represent the record as a tvar so it can later
        unify with a tycon or with another row-constrained tvar. *)
      let rec_lit = List.map rec_lit ~f:(fun (id, x) -> (id, infer env x)) in
      let flds = List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit in
      TERecord (rec_lit, fresh_unbound_var ~row:(ClosedRow flds) ())
    | EWith (rcd, flds) ->
      (* `{r with ...}` requires r to already have at least the new fields
        present (with the new types). Model that as an open-row constraint
        unified with r's type. *)
      let rcd = infer env rcd in
      let rec_lit = List.map flds ~f:(fun (id, x) -> (id, infer env x)) in
      let flds = List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit in
      let row = fresh_unbound_var ~row:(OpenRow flds) () in
      unify env (typ rcd) row;
      TEWith (rcd, rec_lit, typ rcd)
    | EProj (rcd, fld) ->
      let rcd = infer env rcd in
      (* Force before matching: rcd's type may be a Link from earlier
        unification, in which case neither the TyName nor the TyVar arm
        would match without forcing. *)
      (match force (typ rcd) with
      | TyName tname ->
        (* As in unify: a `TyName` may be a rigid (an annotation's type
          parameter) or a nominal tycon. For the rigid path the field
          lookup uses whatever row constraint the rigid carries; for the
          tycon path it uses the tycon's record fields. A rigid with
          `NoRow` has no field information, so projecting from it is a
          type error. *)
        let (flds, name_for_err) =
          match lookup_typevar tname env with
          | Some (OpenRow flds | ClosedRow flds) -> (flds, tname)
          | Some NoRow -> raise (expected_ty_error "record" tname)
          | None ->
            let tc = lookup_tycon tname env in
            (tc.ty, tc.name)
        in
        (match List.Assoc.find flds ~equal fld with
        | Some ty -> TEProj (rcd, fld, ty)
        | _ -> raise (missing_field fld name_for_err))
      | TyVar ({ contents = Unbound(id, row, scope) } as tv) ->
        (* The record type is still a tvar — add an open-row constraint that
          says it must have at least the projected field with some fresh type. *)
        let fld_ty = fresh_unbound_var () in
        let row = union_rows env row (OpenRow [(fld, fld_ty)]) in
        tv := Unbound(id, row, scope);
        TEProj(rcd, fld, fld_ty)
      | ty -> raise (expected_ty_error "TyName or TyVar" (ty_kind ty)))
    | ELet ((id, ann, rhs), body) ->
      (* Standard let-generalization, with two row-aware twists. First,
        when an annotation is present, we turn it rigid: each declared
        parameter `'a` becomes a rigid `TyName "'a"` exposed in the env
        as a `TypeVarBind` carrying its row constraint. The RHS is then
        checked against the annotation's body, with rigids unable to
        unify with anything except themselves. Second, when no annotation
        is given, we generalize the inferred type: any unbound tvar whose
        scope is deeper than the surrounding scope becomes a quantified
        parameter, carrying any row constraint it accumulated. *)
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
      let deduped_defs = Hash_set.create (module String) in
      List.iter decls ~f:(fun (id, _, _) ->
        match Hash_set.strict_add deduped_defs id with
        | Ok _ -> ()
        | Error _ -> raise (duplicate_definition id));
      (* Prepare each decl: turn its annotation rigid (each declared
        parameter becomes a rigid `TyName` plus a `TypeVarBind` entry
        exposed to that decl's own RHS), or assign a fresh unbound tvar
        if there's no annotation. *)
      let prepared = List.map decls ~f:(fun (id, ann, rhs) ->
        match ann with
        | Some ann ->
          let (extras, check_ty) = as_rigid ann in
          (id, Some ann, rhs, extras, check_ty)
        | None ->
          (id, None, rhs, [], fresh_unbound_var ()))
      in
      (* Mutually-recursive value bindings: every decl's check_ty is in
        scope for every decl's RHS, so recursive references typecheck. *)
      let env_decls = List.map prepared ~f:(fun (id, _, _, _, check_ty) ->
        (id, VarBind (dont_generalize check_ty)))
      in
      let env_with_decls = env_decls @ env in
      (* Each RHS sees its own typevars on top of the shared value bindings.
        Distinct decls don't share each other's typevars. *)
      let tdecls : tlet_decl list = List.map prepared ~f:(fun (id, ann, rhs, tv_env, check_ty) ->
        let trhs = check (tv_env @ env_with_decls) check_ty rhs in
        (id, ann, trhs))
      in
      leave_scope();
      (* For each decl, the published type is either the user's annotation
        (already resolved against outer typevars) or the generalized
        inferred type. *)
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

  (* Post-pass: reject any Unbound type variable surviving in the typed AST.
    Generalized tvars are linked away by `gen`, so what's left as Unbound
    is either an anonymous record literal that never got linked to a tycon,
    or an instantiation that wasn't pinned by its surrounding context. *)
  let check_no_unbound (texp : texp) : unit =
    let rec ck_ty (ty : ty) : unit =
      match force ty with
      | TyVar { contents = Unbound (id, _, _) } -> raise (unbound_typevar id)
      | TyVar { contents = Link _ } -> failwith "unexpected: Link after force"
      | TyArrow (from, dst) -> ck_ty from; ck_ty dst
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
    let deduped_defs = Hash_set.create (module String) in
    let env = List.map tl ~f:(fun tc ->
      match Hash_set.strict_add deduped_defs tc.name with
      | Ok _ -> (tc.name, TypeBind tc)
      | Error _ -> raise (duplicate_definition tc.name))
    in
    let texp = infer env exp in
    check_no_unbound texp;
    texp
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
  Poly.equal (ty_pretty (typ x)) "bool"

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
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "if_error" =
  let open Seven() in
  let prog = ([], EIf(EBool true, EBool false, ELam("x", EVar "x"))) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool with ?0 -> ?0")

let%test "record" =
  let open Seven() in
  let prog = (
    [{name = "Foo"; ty = [("x", TyBool); ("y", TyArrow(TyBool, TyBool))]}],
    ELet(("foo", Some {type_params = []; ty = TyName "Foo"},
          ERecord [("x", EBool true); ("y", ELam("x", EVar "x"))]),
      EApp(EProj(EVar "foo", "y"), EBool true))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let" =
  let open Seven() in
  let prog = (
    [{name = "A"; ty = [("x", TyBool)]}],
    ELet(("r", Some {type_params = []; ty = TyName "A"},
          ERecord [("x", EBool true)]),
      EProj(EVar "r", "x"))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let_ann" =
  let open Seven() in
  let prog = (
    [{name = "A"; ty = []}],
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
  )) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let_rec_error" =
  let open Seven() in
  let prog = (
    [{name = "A"; ty = []}],
    ELetRec(
      [("f", None, ELam("x", EIf(EVar "x", EApp(EVar "g", EVar "x"), EVar "x")));
       ("g", Some {type_params = []; ty = TyArrow(TyBool, TyName "A")},
        ELam("x", EIf(EVar "x", EApp(EVar "f", EVar "x"),
          ELet(("a", Some {type_params = []; ty = TyName "A"}, ERecord []),
            EVar "a"))))],
      EApp(EVar "f", EBool true))
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type A with bool")

let%test "let_gen" =
  let open Seven() in
  let prog = (
    [{name = "A"; ty = []}],
    ELet(("a", Some {type_params = []; ty = TyName "A"}, ERecord []),
      ELet(("f", None, ELam("x", EVar "x")),
        ELet(("_", None, EApp(EVar "f", EVar "a")),
          EApp(EVar "f", EBool true))))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "fix" =
  let open Seven() in
  let prog = ([],
    ELetRec([("fix", None,
      ELam("f", ELam("x", EApp(EApp(EVar "f", EApp(EVar "fix", EVar "f")), EVar "x"))))],
      EApp(EVar "fix",
        ELam("f", ELam("arg",
          EIf(EVar "arg", EApp(EVar "f", EBool false), EBool true)))))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool -> bool"

let%test "let_gen_ann" =
  let open Seven() in
  let prog = (
    [{name = "A"; ty = []}],
    ELet(("a", Some {type_params = []; ty = TyName "A"}, ERecord []),
      ELet(("f", Some {type_params = [("'a", NoRow)]; ty = TyArrow(TyName "'a", TyBool)},
        ELam("x", EBool true)),
        EApp(EVar "f", EVar "a")))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let_gen_error" =
  let open Seven() in
  let prog = (
    [{name = "A"; ty = []}],
    ELet(("f", Some {type_params = [("'a", NoRow)]; ty = TyArrow(TyName "'a", TyName "A")},
      ELam("x", EBool true)),
      EApp(EVar "f", EBool true))
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type 'a -> A")

let%test "let_gen_scope_error" =
  let open Seven() in
  let prog = ([],
    EApp(EApp(ELam("x", ELet(("y", None, EVar "x"), EVar "y")), EBool true), EBool true)
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool with bool -> ?2")

(* Row-polymorphic generalization: `let f r = r.x` should give f a forall
  with an open-row constraint on its parameter type. We exercise that by
  applying f to two records of *different* nominal tycons in sequence,
  each with its own `x` field type — f instantiates freshly per use. *)
let%test "let_gen_row" =
  let open Seven() in
  let prog = (
    [{name = "Foo"; ty = [("x", TyBool)]};
     {name = "Bar"; ty = [("x", TyArrow(TyBool, TyBool))]}],
    ELet(("f", None, ELam("r", EProj(EVar "r", "x"))),
      ELet(("r1", Some {type_params = []; ty = TyName "Foo"}, ERecord [("x", EBool true)]),
        ELet(("r2", Some {type_params = []; ty = TyName "Bar"},
              ERecord [("x", ELam("y", EVar "y"))]),
          ELet(("_", None, EApp(EVar "f", EVar "r1")),
            EApp(EVar "f", EVar "r2")))))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool -> bool"

(* TypeVarBind for let: a nested annotation mentioning 'a from an outer
  annotated let resolves to the outer let's tvar. *)
let%test "let_typevar_ref" =
  let open Seven() in
  let prog = ([],
    ELet(("f",
      Some {type_params = [("'a", NoRow)]; ty = TyArrow(TyName "'a", TyName "'a")},
      ELam("x", ELet(("y", Some {type_params = []; ty = TyName "'a"}, EVar "x"), EVar "y"))),
      EApp(EVar "f", EBool true))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

(* TypeVarBind for let rec: same idea, but the typevars are introduced by
  a recursive decl's annotation and used by that decl's own RHS. *)
let%test "let_rec_typevar_ref" =
  let open Seven() in
  let prog = ([],
    ELetRec(
      [("f",
        Some {type_params = [("'a", NoRow)]; ty = TyArrow(TyName "'a", TyName "'a")},
        ELam("x", ELet(("y", Some {type_params = []; ty = TyName "'a"}, EVar "x"), EVar "y")))],
      EApp(EVar "f", EBool true))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

(* Rigid identity: `forall 'a. 'a -> 'a = fun x -> x` should pass.
  The parameter ?p unifies with rigid 'a (NoRow, OK), then the body's
  return type is forced to 'a too, which matches. *)
let%test "let_rigid_ok" =
  let open Seven() in
  let prog = ([],
    ELet(("f",
      Some {type_params = [("'a", NoRow)]; ty = TyArrow(TyName "'a", TyName "'a")},
      ELam("x", EVar "x")),
      EApp(EVar "f", EBool true))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

(* Rigid rejection: `forall 'a, 'b. 'a -> 'b = fun x -> x` should fail.
  After unifying ?p with 'a, the second unify of ?p with 'b forces 'a
  and 'b to be the same TyName, which they aren't. *)
let%test "let_rigid_error" =
  let open Seven() in
  let prog = ([],
    ELet(("f",
      Some {type_params = [("'a", NoRow); ("'b", NoRow)];
            ty = TyArrow(TyName "'a", TyName "'b")},
      ELam("x", EVar "x")),
      EVar "f")
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type 'a -> 'b")

(* Same rejection works inside `letrec`: each decl's annotation is
  turned rigid, with rigid names exposed only to that decl's own RHS. *)
let%test "let_rec_rigid_error" =
  let open Seven() in
  let prog = ([],
    ELetRec(
      [("f",
        Some {type_params = [("'a", NoRow); ("'b", NoRow)];
              ty = TyArrow(TyName "'a", TyName "'b")},
        ELam("x", EVar "x"))],
      EVar "f")
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type 'a -> 'b")
