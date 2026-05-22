open Base
open Poly

module Nine() = struct
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
  (* A row constraint sits on an unbound type variable. *)
  and row_constraint =
    | NoRow
    | OpenRow of record_ty (* Must contain at least these fields. *)
    | ClosedRow of record_ty (* Must contain exactly these fields. *)
  and tv = (* A type variable *)
    | Unbound of id * row_constraint * scope
    | Link of ty
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

  let ty_kind (ty : ty) =
    match ty with
    | TyBool -> "TyBool"
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
    | TyVar { contents = Unbound(id, NoRow, _) } -> id
    | TyVar { contents = Unbound(id, OpenRow flds, _) } ->
      Printf.sprintf "%s{%s}" id (ty_fields ty_pretty flds)
    | TyVar { contents = Unbound(_, ClosedRow flds, _) } ->
      Printf.sprintf "{%s}" (ty_fields ty_pretty flds)
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
    | TyVar { contents = Unbound(id, OpenRow flds, scope) } ->
      Printf.sprintf "TyVar(Unbound(%s, OpenRow{%s}, %d))" id (ty_fields ty_debug flds) scope
    | TyVar { contents = Unbound(id, ClosedRow flds, scope) } ->
      Printf.sprintf "TyVar(Unbound(%s, ClosedRow{%s}, %d))" id (ty_fields ty_debug flds) scope
    | TyArrow(from, dst) ->
      "(" ^ ty_debug from ^ " -> " ^ ty_debug dst ^ ")"
    | TyName name -> name
    | TyApp app -> String.concat ~sep:" " (List.map app ~f:ty_debug)

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

  let lookup_binding name (e : env) : bind =
    match List.Assoc.find e ~equal name with
    | Some b -> b
    | None -> raise (undefined_error "type" name)

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

  let rec is_value (x: texp) : bool =
    match x with
    | TEBool _ | TEVar _ | TELam _ -> true
    | TERecord (rec_lit, _) -> List.for_all rec_lit ~f:(fun (_, fld) -> is_value fld)
    | TEWith _ | TEApp _ | TEIf _ | TEProj _ | TELet _ | TELetRec _ -> false

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

  let apply_tyapp env (ty : ty) : record_ty option =
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
    | TyApp (TyName name :: args) ->
      (match lookup_binding name env with
       | TypeBind tc ->
         (match List.zip tc.type_params args with
          | Ok pairs ->
            let tbl = Hashtbl.of_alist_exn (module String) pairs in
            Some (List.map tc.ty ~f:(fun (id, t) -> (id, substitute tbl t)))
          | Unequal_lengths -> None)
       | TypeVarBind _ | VarBind _ -> raise (undefined_error "type" name))
    | _ -> None

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
    match force ty with
    | TyVar tgt when src == tgt -> raise OccursCheck
    | TyVar ({ contents = Unbound (id, tgt_row, tgt_scope) } as tgt) ->
      row_iter tgt_row (fun (_, ty) -> occurs src ty);
      let { contents = Unbound(_, _, src_scope) } = src in
      let min_scope = min src_scope tgt_scope in
      tgt := Unbound (id, tgt_row, min_scope)
    | TyArrow(from, dst) ->
      occurs src from;
      occurs src dst;
    | TyApp app -> List.iter app ~f:(occurs src)
    | _ -> ()

  (* Check that tv_row's fields are contained within rigid_row. *)
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
    let t1, t2 = (force t1, force t2) in
    match (t1, t2) with
    | _ when equal t1 t2 -> ()
    | TyArrow (f1, d1), TyArrow (f2, d2) ->
      unify env f1 f2;
      unify env d1 d2;
    | TyVar tv, ty | ty, TyVar tv ->
      let Unbound(_, tv_row, src_scope) = !tv in
      (match ty with
      | TyName tname ->
        (match lookup_binding tname env with
         | TypeVarBind rigid_row -> check_rigid_subset env tv_row rigid_row
         | TypeBind tc when List.is_empty tc.type_params ->
           ignore (union_rows env tv_row (ClosedRow tc.ty))
         | TypeBind _ -> raise (unify_failed t1 t2)
         | VarBind _ -> raise (undefined_error "type" tname))
      | TyApp _ ->
        (match apply_tyapp env ty with
         | Some flds -> ignore (union_rows env tv_row (ClosedRow flds))
         | None -> raise (unify_failed t1 t2))
      | TyVar other when tv != other ->
        let Unbound(id, other_row, other_scope) = !other in
        row_iter other_row (fun (_, ty) -> occurs tv ty);
        let min_scope = min src_scope other_scope in
        let row = union_rows env tv_row other_row in
        other := Unbound(id, row, min_scope)
      | _ when equal tv_row NoRow -> occurs tv ty
      | _ -> raise (unify_failed t1 t2));
      tv := Link ty
    | TyName a, TyName b when equal a b -> ()
    | TyApp app1, TyApp app2 when List.length app1 = List.length app2 ->
      List.iter2_exn app1 app2 ~f:(unify env)
    | _ -> raise (unify_failed t1 t2)

  (* The environment stores generic types, but sometimes we need to associate
    a non-generalized type to a variable. This function wraps a type into a
    trivial generic type (no quantified parameters). *)
  let dont_generalize ty : generic_ty = { type_params = []; ty }

  let gen (ty: ty) : generic_ty =
    let type_params : (id, row_constraint) Hashtbl.t = Hashtbl.create (module String) in
    let rec gen' ty =
      match force ty with
      | TyVar ({ contents = Unbound (id, row, scope) } as tv) when scope > !current_scope ->
        Hashtbl.set type_params ~key:id ~data:(gen_row row);
        (* Mutate the tvar to Link to its generalized TyName, so the
          post-pass walking the AST doesn't see it as Unbound. *)
        tv := Link (TyName id);
        TyName id
      | TyArrow (from, dst) -> TyArrow (gen' from, gen' dst)
      | TyApp app -> TyApp (List.map app ~f:gen')
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
    let inst_row row =
      match row with
      | NoRow -> NoRow
      | OpenRow flds -> OpenRow (List.map flds ~f:(fun (id, ty) -> (id, inst' ty)))
      | ClosedRow flds -> ClosedRow (List.map flds ~f:(fun (id, ty) -> (id, inst' ty)))
    in
    (* Attach the instantiated row constraint to each fresh type variable in the table. *)
    List.iter gty.type_params ~f:(fun (pid, row) ->
      match row with
      | NoRow -> ()
      | _ ->
        let TyVar tv = Hashtbl.find_exn tbl pid in
        let Unbound(id, _, scope) = !tv in
        tv := Unbound(id, inst_row row, scope));
    inst' gty.ty

  (* Turn a generic_ty into its rigid form, so that when annotations are instantiated,
     they don't produce Unbound type variables that can unify with each other.*)
  let as_rigid (gty: generic_ty) : env * ty =
    let extras = List.map gty.type_params ~f:(fun (id, row) -> (id, TypeVarBind row)) in
    (extras, gty.ty)

  let generalize_if_value rhs : generic_ty =
    if is_value rhs then gen (typ rhs)
    else dont_generalize (typ rhs)

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
      (match force (typ rcd) with
      | TyName tname ->
        let (flds, name_for_err) =
          match lookup_binding tname env with
          | TypeVarBind (OpenRow flds | ClosedRow flds) -> (flds, tname)
          | TypeVarBind NoRow -> raise (expected_ty_error "record" tname)
          | TypeBind tc -> (tc.ty, tc.name)
          | VarBind _ -> raise (undefined_error "type" tname)
        in
        (match List.Assoc.find flds ~equal fld with
        | Some ty -> TEProj (rcd, fld, ty)
        | _ -> raise (missing_field fld name_for_err))
      | TyApp _ as ty_app ->
        (match apply_tyapp env ty_app with
         | Some flds ->
           (match List.Assoc.find flds ~equal fld with
            | Some ty -> TEProj (rcd, fld, ty)
            | _ ->
              let name = (match ty_app with
                | TyApp (TyName n :: _) -> n
                | _ -> ty_kind ty_app)
              in
              raise (missing_field fld name))
         | None -> raise (expected_ty_error "TyApp" (ty_kind ty_app)))
      | TyVar ({ contents = Unbound(id, row, scope) } as tv) ->
        let fld_ty = fresh_unbound_var () in
        let row = union_rows env row (OpenRow [(fld, fld_ty)]) in
        tv := Unbound(id, row, scope);
        TEProj(rcd, fld, fld_ty)
      | ty -> raise (expected_ty_error "TyName, TyApp, or TyVar" (ty_kind ty)))
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
      (* Value restriction: only generalize if the RHS is a value. *)
      let ty_gen =
        match ann with
        | Some ann -> ann
        | None -> generalize_if_value rhs
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
          | None -> generalize_if_value rhs
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
  let open Nine() in
  let prog = ([], EApp(ELam("x", EVar "x"), EBool true)) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "basic_error" =
  let open Nine() in
  let prog = ([], EApp(ELam("f", EApp(EVar "f", EBool true)), EBool true)) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool -> ?1 with bool")

let%test "if" =
  let open Nine() in
  let prog = ([], EIf(EBool true, EBool false, EApp(ELam("x", EVar "x"), EBool true))) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "if_error" =
  let open Nine() in
  let prog = ([], EIf(EBool true, EBool false, ELam("x", EVar "x"))) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool with ?0 -> ?0")

let%test "record_via_unparameterized_tycon" =
  let open Nine() in
  let prog = (
    [{name = "Foo"; type_params = []; ty = [("x", TyBool); ("y", TyArrow(TyBool, TyBool))]}],
    ELet(("foo", Some {type_params = []; ty = TyName "Foo"},
          ERecord [("x", EBool true); ("y", ELam("x", EVar "x"))]),
      EApp(EProj(EVar "foo", "y"), EBool true))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let" =
  let open Nine() in
  let prog = (
    [{name = "A"; type_params = []; ty = [("x", TyBool)]}],
    ELet(("r", Some {type_params = []; ty = TyName "A"},
          ERecord [("x", EBool true)]),
      EProj(EVar "r", "x"))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let_ann" =
  let open Nine() in
  let prog = (
    [{name = "A"; type_params = []; ty = []}],
    ELet(("x", Some { type_params = []; ty = TyName "A" }, EBool true), EVar "x")
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type A")

let%test "let_rec" =
  let open Nine() in
  let prog = ([], ELetRec(
    [("f", None, ELam("x", EIf(EVar "x", EApp(EVar "g", EVar "x"), EVar "x")));
     ("g", None, ELam("x", EIf(EVar "x", EApp(EVar "f", EVar "x"), EVar "x")))],
    EApp(EVar "f", EBool true)
  )) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let_rec_error" =
  let open Nine() in
  let prog = (
    [{name = "A"; type_params = []; ty = []}],
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
  let open Nine() in
  let prog = (
    [{name = "A"; type_params = []; ty = []}],
    ELet(("a", Some {type_params = []; ty = TyName "A"}, ERecord []),
      ELet(("f", None, ELam("x", EVar "x")),
        ELet(("_", None, EApp(EVar "f", EVar "a")),
          EApp(EVar "f", EBool true))))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "fix" =
  let open Nine() in
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
  let open Nine() in
  let prog = (
    [{name = "A"; type_params = []; ty = []}],
    ELet(("a", Some {type_params = []; ty = TyName "A"}, ERecord []),
      ELet(("f", Some {type_params = [("'a", NoRow)]; ty = TyArrow(TyName "'a", TyBool)},
        ELam("x", EBool true)),
        EApp(EVar "f", EVar "a")))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let_gen_error" =
  let open Nine() in
  let prog = (
    [{name = "A"; type_params = []; ty = []}],
    ELet(("f", Some {type_params = [("'a", NoRow)]; ty = TyArrow(TyName "'a", TyName "A")},
      ELam("x", EBool true)),
      EApp(EVar "f", EBool true))
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (TypeError "expression does not have type 'a -> A")

let%test "let_gen_scope_error" =
  let open Nine() in
  let prog = ([],
    EApp(EApp(ELam("x", ELet(("y", None, EVar "x"), EVar "y")), EBool true), EBool true)
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool with bool -> ?2")

let%test "let_typevar_ref" =
  let open Nine() in
  let prog = ([],
    ELet(("f",
      Some {type_params = [("'a", NoRow)]; ty = TyArrow(TyName "'a", TyName "'a")},
      ELam("x", ELet(("y", Some {type_params = []; ty = TyName "'a"}, EVar "x"), EVar "y"))),
      EApp(EVar "f", EBool true))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let_rec_typevar_ref" =
  let open Nine() in
  let prog = ([],
    ELetRec(
      [("f",
        Some {type_params = [("'a", NoRow)]; ty = TyArrow(TyName "'a", TyName "'a")},
        ELam("x", ELet(("y", Some {type_params = []; ty = TyName "'a"}, EVar "x"), EVar "y")))],
      EApp(EVar "f", EBool true))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let_rigid_ok" =
  let open Nine() in
  let prog = ([],
    ELet(("f",
      Some {type_params = [("'a", NoRow)]; ty = TyArrow(TyName "'a", TyName "'a")},
      ELam("x", EVar "x")),
      EApp(EVar "f", EBool true))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "let_rigid_error" =
  let open Nine() in
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

let%test "let_rec_rigid_error" =
  let open Nine() in
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

let%test "let_gen_row" =
  let open Nine() in
  let prog = (
    [{name = "Foo"; type_params = []; ty = [("x", TyBool)]};
     {name = "Bar"; type_params = []; ty = [("x", TyArrow(TyBool, TyBool))]}],
    ELet(("f", None, ELam("r", EProj(EVar "r", "x"))),
      ELet(("r1", Some {type_params = []; ty = TyName "Foo"}, ERecord [("x", EBool true)]),
        ELet(("r2", Some {type_params = []; ty = TyName "Bar"},
              ERecord [("x", ELam("y", EVar "y"))]),
          ELet(("_", None, EApp(EVar "f", EVar "r1")),
            EApp(EVar "f", EVar "r2")))))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool -> bool"

let%test "generic_tycon" =
  let open Nine() in
  let prog = (
    [{name = "box"; type_params = ["'a"]; ty = [("x", TyName "'a")]}],
    ELet(("r",
      Some {type_params = []; ty = TyApp [TyName "box"; TyBool]},
      ERecord [("x", EBool true)]),
      EProj(EVar "r", "x"))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "generic_tycon_let_gen" =
  let open Nine() in
  let prog = (
    [{name = "box"; type_params = ["'a"]; ty = [("x", TyName "'a")]}],
    ELet(("identity",
      Some {type_params = [("'a", NoRow)];
            ty = TyArrow(TyApp [TyName "box"; TyName "'a"],
                         TyApp [TyName "box"; TyName "'a"])},
      ELam("b", EVar "b")),
      EApp(EVar "identity",
        ELet(("r",
          Some {type_params = []; ty = TyApp [TyName "box"; TyBool]},
          ERecord [("x", EBool true)]),
          EVar "r")))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "box bool"

let%test "generic_tycon_error" =
  let open Nine() in
  let prog = (
    [{name = "box"; type_params = ["'a"]; ty = [("x", TyName "'a"); ("y", TyBool)]}],
    ELet(("r",
      Some {type_params = []; ty = TyApp [TyName "box"; TyBool]},
      ERecord [("x", EBool true)]),
      EProj(EVar "r", "x"))
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (RowMismatch "ClosedRow{x: bool} and ClosedRow{x: bool, y: bool}")

let%test "value_restriction" =
  let open Nine() in
  let prog = (
    [
      {name = "Ref"; type_params = ["'a"]; ty = [("value", TyName "'a")]};
      {name = "Unit"; type_params = []; ty = []}
    ],
    ELet(("ref", Some {type_params = [("'a", NoRow)];
      ty = TyArrow(TyName "'a", TyApp [TyName "Ref"; TyName "'a"])},
      ELam("x", ERecord [("value", EVar "x")])),
    ELet(("deref", Some {type_params = [("'a", NoRow)];
      ty = TyArrow(TyApp [TyName "Ref"; TyName "'a"], TyName "'a")},
      ELam("r", EProj(EVar "r", "value"))),
    ELet(("update", Some {type_params = [("'a", NoRow)];
      ty = TyArrow(TyApp [TyName "Ref"; TyName "'a"],
            TyArrow(TyName "'a", TyName "Unit"))},
      ELam("r", ELam("x", ERecord []))),
    ELet(("r", None, EApp(EVar "ref", ELam("x", EVar "x"))),
    ELet(("_", None, EApp(EApp(EVar "update", EVar "r"),
      ELam("x", EIf(EVar "x", EBool false, EBool true)))),
    EApp(EApp(EVar "update", EVar "r"), ELam("x", EBool false)))))))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "Unit"

let%test "value_restriction_error" =
  let open Nine() in
  let prog = (
    [
      {name = "Ref"; type_params = ["'a"]; ty = [("value", TyName "'a")]};
      {name = "Unit"; type_params = []; ty = []}
    ],
    ELet(("ref", Some {type_params = [("'a", NoRow)];
      ty = TyArrow(TyName "'a", TyApp [TyName "Ref"; TyName "'a"])},
      ELam("x", ERecord [("value", EVar "x")])),
    ELet(("deref", Some {type_params = [("'a", NoRow)];
      ty = TyArrow(TyApp [TyName "Ref"; TyName "'a"], TyName "'a")},
      ELam("r", EProj(EVar "r", "value"))),
    ELet(("update", Some {type_params = [("'a", NoRow)];
      ty = TyArrow(TyApp [TyName "Ref"; TyName "'a"],
            TyArrow(TyName "'a", TyName "Unit"))},
      ELam("r", ELam("x", ERecord []))),
    ELet(("r", None, EApp(EVar "ref", ELam("x", EVar "x"))),
    ELet(("_", None, EApp(EApp(EVar "update", EVar "r"),
      ELam("x", EIf(EVar "x", EBool false, EBool true)))),
    ELet(("u", Some {type_params = []; ty = TyName "Unit"}, ERecord []),
      EApp(EApp(EVar "deref", EVar "r"), EVar "u")))))))
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (UnificationFailure "failed to unify type bool with Unit")

let%test "row_ann" =
  let open Nine() in
  let prog = (
    [{name = "Foo"; type_params = []; ty = [("x", TyBool); ("y", TyBool)]}],
    ELet(("get_x",
      Some {type_params = [("'r", OpenRow [("x", TyBool)])];
            ty = TyArrow(TyName "'r", TyBool)},
      ELam("r", EProj(EVar "r", "x"))),
    ELet(("foo", Some {type_params = []; ty = TyName "Foo"},
      ERecord [("x", EBool true); ("y", EBool false)]),
      EApp(EVar "get_x", EVar "foo")))
  ) in
  let x = typecheck_prog prog in
  Poly.equal (ty_pretty (typ x)) "bool"

let%test "row_ann_missing_field" =
  let open Nine() in
  let prog = (
    [{name = "Foo"; type_params = []; ty = [("y", TyBool)]}],
    ELet(("get_x",
      Some {type_params = [("'r", OpenRow [("x", TyBool)])];
            ty = TyArrow(TyName "'r", TyBool)},
      ELam("r", EProj(EVar "r", "x"))),
    ELet(("foo", Some {type_params = []; ty = TyName "Foo"},
      ERecord [("y", EBool true)]),
      EApp(EVar "get_x", EVar "foo")))
  ) in
  assert_raises
    (fun () -> typecheck_prog prog)
    (RowMismatch "OpenRow{x: bool} and ClosedRow{y: bool}")
