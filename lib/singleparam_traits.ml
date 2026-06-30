open Base
open Poly
open Mini_ml

module Singleparam_traits() = struct
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
  (* A predicate Tr t states that the type t satisfies the trait Tr. *)
  type pred = { trait : id; arg : ty }
  (* A generic type. Should be read as forall p1::r1..pn::rn. P1, ..., Pk => ty,
    where each pi is a type parameter with row constraint ri (NoRow for
    plain parameters) and each Pj is a predicate that the type parameters
    must satisfy. It is separated from ty because in HM, a forall can only
    be at the top level of a type. *)
  type generic_ty = {
    type_params : (id * row_constraint) list;
    predicates : pred list;
    ty : ty;
  }
  (* Trait declaration with a type parameter and methods. *)
  type trait_decl = {
    name : id;
    type_param : id;
    methods : record_ty;
  }
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
  (* An instance declaration carries evidence that some type satisfies a trait,
    assuming the predicates in the context hold. *)
  type instance_decl = {
    head : pred;
    type_params : id list;
    context : pred list;
    methods : record_lit;
  }
  type bind =
    | VarBind of generic_ty (* A variable binding maps to a generic type. *)
    | TypeBind of tycon (* A type binding maps to a type constructor. *)
    | TypeVarBind of row_constraint
      (* A type variable binding marks some rigid type and its corresponding row constraints. *)
    | InstanceBind of instance_decl
      (* A global instance declaration. *)
    | GivenBind of pred
      (* A predicate that is given to the environment by an annotation or instance context. *)
  type env = (id * bind) list
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
  type prog = tycon list * trait_decl list * instance_decl list * exp

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

  let print_pred f (p : pred) = p.trait ^ " " ^ f p.arg

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
  exception NoSuchInstance of string
  exception MatchFailure

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

  let no_instance preds =
    NoSuchInstance
      (Printf.sprintf "no instance found for %s"
         (String.concat ~sep:", " (List.map preds ~f:(print_pred ty_pretty))))

  let cannot_apply name =
    UnificationFailure (Printf.sprintf "cannot apply %s" name)

  let missing_method trait_name mname =
    TypeError (Printf.sprintf "instance for trait %s is missing method %s" trait_name mname)

  let undeclared_method mname trait_name =
    TypeError (Printf.sprintf "method %s is not declared in trait %s" mname trait_name)

  (* Lookup a variable's type in the environment. *)
  let lookup_var_type name (e : env) : generic_ty =
    match List.Assoc.find e ~equal name with
    | Some (VarBind t) -> t
    | _ -> raise (undefined_error "variable" name)

  let lookup_binding name (e : env) : bind =
    match List.Assoc.find e ~equal name with
    | Some b -> b
    | None -> raise (undefined_error "type" name)

  let find_trait traits name : trait_decl =
    match List.find traits ~f:(fun t -> String.equal t.name name) with
    | Some t -> t
    | None -> raise (undefined_error "trait" name)

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
  (* Global state that stores the trait predicates emitted during type inference. *)
  let emitted : pred list ref = ref []

  (* Prepend predicate to the emitted list. *)
  let emit (p : pred) = emitted := p :: !emitted

  (* Remove the predicates from emitted that satisfy f and return them. *)
  let take_emitted ~f =
    let matched, kept =
      List.fold !emitted ~init:([], []) ~f:(fun (m, k) p ->
        if f p then (p :: m, k) else (m, p :: k))
    in
    emitted := kept;
    matched


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

  (* Walk a type, replacing any TyName whose id appears in tbl with the
     corresponding entry. *)
  let rec substitute (tbl : (id, ty) Hashtbl.t) (ty : ty) : ty =
    match force ty with
    | TyName id as ty ->
      (match Hashtbl.find tbl id with
       | Some t -> t
       | None -> ty)
    | TyArrow (from, dst) -> TyArrow (substitute tbl from, substitute tbl dst)
    | TyApp app -> TyApp (List.map app ~f:(substitute tbl))
    | ty -> ty

  let apply_tyapp env (ty : ty) : record_ty =
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

  (* A one-way match mirroring the structure of unify. *)
  let rec match_ty (pattern : ty) (target : ty) : unit =
    let pattern, target = (force pattern, force target) in
    match (pattern, target) with
    | _ when equal pattern target -> ()
    | TyArrow (f1, d1), TyArrow (f2, d2) ->
      match_ty f1 f2;
      match_ty d1 d2
    | TyVar tv, ty ->
      occurs tv ty;
      tv := Link ty
    | TyName a, TyName b when equal a b -> ()
    | TyApp app1, TyApp app2 when List.length app1 = List.length app2 ->
      List.iter2_exn app1 app2 ~f:match_ty
    | _ -> raise MatchFailure

  (* The environment stores generic types, but sometimes we need to associate
    a non-generalized type to a variable. This function wraps a type into a
    trivial generic type (no quantified parameters). *)
  let dont_generalize ty : generic_ty = { type_params = []; predicates = []; ty }

  (* The scope of a predicate is the outermost scope of the type variables it
     mentions. *)
  let scope_of_pred (p : pred) : int =
    let rec scope_of_ty acc ty =
      match force ty with
      | TyVar { contents = Unbound (_, row, scope) } ->
        min (scope_of_row acc row) scope
      | TyArrow (a, b) -> scope_of_ty (scope_of_ty acc a) b
      | TyApp tys -> List.fold tys ~init:acc ~f:scope_of_ty
      | TyVar { contents = Link _ } | TyBool | TyName _ -> acc
    and scope_of_row acc = function
      | NoRow -> acc
      | OpenRow flds | ClosedRow flds ->
        List.fold flds ~init:acc ~f:(fun acc (_, ty) -> scope_of_ty acc ty)
    in
    scope_of_ty Int.max_value p.arg

  (* Wrap match_ty into a bool-returning variant for matching attempts. *)
  let try_match (pattern : ty) (target : ty) : bool =
    try match_ty pattern target; true
    with MatchFailure | OccursCheck -> false

  (* Scan through trait bindings in the env to see if the predicate matches against any of them. *)
  let rec resolve_pred env (p : pred) : bool =
    List.exists env ~f:(fun (_, b) -> match b with
      | GivenBind g ->
        String.equal g.trait p.trait && try_match g.arg p.arg
      | InstanceBind inst when String.equal inst.head.trait p.trait ->
        let tbl = Hashtbl.of_alist_exn (module String)
          (List.map inst.type_params ~f:(fun pid -> (pid, fresh_unbound_var ())))
        in
        let inst_arg = substitute tbl inst.head.arg in
        let inst_context = List.map inst.context ~f:(fun c ->
          { c with arg = substitute tbl c.arg })
        in
        try_match inst_arg p.arg
        && List.for_all inst_context ~f:(resolve_pred env)
      | _ -> false)

  (* Remove from emitted any predicates that have a matching trait binding in env. *)
  let resolve_emitted env = ignore (take_emitted ~f:(resolve_pred env))

  (* Take predicates in our current scope. *)
  let take_scoped_preds () =
    take_emitted ~f:(fun p -> scope_of_pred p > !current_scope)

  let gen ~to_link ~(scoped_preds : pred list) (ty: ty) : generic_ty =
    let type_params : (id, row_constraint) Hashtbl.t = Hashtbl.create (module String) in
    let rec gen' ty =
      match force ty with
      | TyVar ({ contents = Unbound (id, row, scope) } as tv) when scope > !current_scope ->
        Hashtbl.set type_params ~key:id ~data:(map_row ~f:gen' row);
        (* Record the tvar so the caller can Link it to its generalized
          TyName after all related bindings have been generalized. *)
        to_link := tv :: !to_link;
        TyName id
      | TyArrow (from, dst) -> TyArrow (gen' from, gen' dst)
      | TyApp app -> TyApp (List.map app ~f:gen')
      | ty -> ty
    in
    let ty = gen' ty in
    let predicates =
      List.map scoped_preds ~f:(fun p -> { p with arg = gen' p.arg })
    in
    let type_params =
      Hashtbl.to_alist type_params
      |> List.sort ~compare:(fun (a,_) (b,_) -> String.compare a b)
    in
    { type_params; predicates; ty }

  (* Link each recorded tvar to its generalized TyName, so the
     post-pass walking the AST doesn't see it as Unbound. *)
  let link_all to_link =
    List.iter !to_link ~f:(fun tv ->
      match !tv with
      | Unbound (id, _, _) -> tv := Link (TyName id)
      | Link _ -> ())

  (* Instantiate a generic type by replacing all the type parameters
   with fresh unbound type variables. Ensure that the same ID gets
   mapped to the same unbound type variable by using an (id, ty) Hashtbl. *)
  let inst (gty: generic_ty) : ty =
    let tbl = Hashtbl.of_alist_exn (module String)
      (List.map gty.type_params ~f:(fun (pid, _) -> (pid, fresh_unbound_var ())))
    in
    (* Attach the instantiated row constraint to each fresh type variable in the table. *)
    List.iter gty.type_params ~f:(fun (pid, row) ->
      match row with
      | NoRow -> ()
      | _ ->
        let TyVar tv = Hashtbl.find_exn tbl pid in
        let Unbound(id, _, scope) = !tv in
        tv := Unbound(id, map_row ~f:(substitute tbl) row, scope));
    (* Emit each predicate with its argument substituted with the
       fresh type variable from the table. *)
    List.iter gty.predicates ~f:(fun p ->
      emit { p with arg = substitute tbl p.arg });
    substitute tbl gty.ty

  (* Turn a generic_ty into its rigid form, so that when annotations are instantiated,
     they don't produce Unbound type variables that can unify with each other.*)
  let as_rigid (gty: generic_ty) : env * ty =
    let type_var_extras = List.map gty.type_params ~f:(fun (id, row) -> (id, TypeVarBind row)) in
    let trait_extras = List.map gty.predicates ~f:(fun p -> ("_given", GivenBind p)) in
    (type_var_extras @ trait_extras, gty.ty)

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
          let env' = extras @ env in
          let trhs = check env' check_ty rhs in
          resolve_emitted env';
          trhs
        | None -> infer env rhs
      in
      leave_scope ();
      let to_link = ref [] in
      (* Value restriction: only generalize if the RHS is a value. *)
      let ty_gen =
        match ann with
        | Some ann -> ann
        | None when is_value rhs ->
          let scoped_preds = take_scoped_preds () in
          gen ~to_link ~scoped_preds (typ rhs)
        | None -> dont_generalize (typ rhs)
      in
      link_all to_link;
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
        let env' = extras @ env_with_decls in
        let trhs = check env' check_ty rhs in
        resolve_emitted env';
        (id, ann, trhs))
      in
      leave_scope ();
      let any_value_unannotated =
        List.exists tdecls ~f:(fun (_, ann, t) -> ann = None && is_value t)
      in
      let scoped_preds = if any_value_unannotated then take_scoped_preds () else [] in
      let to_link = ref [] in
      let generalized_bindings = List.map tdecls ~f:(fun (id, ann, rhs) ->
        let ty_gen =
          match ann with
          | Some ann -> ann
          | None when is_value rhs -> gen ~to_link ~scoped_preds (typ rhs)
          | None -> dont_generalize (typ rhs)
        in
        (id, VarBind ty_gen))
      in
      (* Link tvars only after all bindings have been generalized, otherwise
        the TyName would be hidden when trying to generalize the next binding. *)
      link_all to_link;
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

  let typecheck_prog ((tycons, traits, instances, exp): prog) : texp =
    let env_tycons = List.map tycons ~f:(fun tc -> (tc.name, TypeBind tc)) in
    (* Add trait methods to the env. *)
    let env_traits = List.concat_map traits ~f:(fun tr ->
      List.map tr.methods ~f:(fun (mname, mty) ->
        (mname, VarBind {
          type_params = [(tr.type_param, NoRow)];
          predicates = [{ trait = tr.name; arg = TyName tr.type_param }];
          ty = mty;
        })))
    in
    let env_instances = List.map instances ~f:(fun inst -> ("_instance", InstanceBind inst)) in
    let env = env_tycons @ env_traits @ env_instances in
    List.iter tycons ~f:(wf_tycon env);
    (* Check each instance's method bodies against the trait's method signatures. *)
    List.iter instances ~f:(fun inst ->
      let trait = find_trait traits inst.head.trait in
      let tbl = Hashtbl.of_alist_exn (module String) [(trait.type_param, inst.head.arg)] in
      List.iter trait.methods ~f:(fun (mname, _) ->
        if not (List.exists inst.methods ~f:(fun (n, _) -> String.equal n mname)) then
          raise (missing_method inst.head.trait mname));
      List.iter inst.methods ~f:(fun (mname, mbody) ->
        let mty_sig =
          match List.Assoc.find trait.methods mname ~equal:String.equal with
          | Some s -> s
          | None -> raise (undeclared_method mname trait.name)
        in
        let gty : generic_ty = {
          type_params = List.map inst.type_params ~f:(fun p -> (p, NoRow));
          predicates = inst.context;
          ty = substitute tbl mty_sig;
        } in
        let (extras, check_ty) = as_rigid gty in
        let env' = extras @ env in
        let _ = check env' check_ty mbody in
        resolve_emitted env'));
    let texp = infer env exp in
    resolve_emitted env;
    if not (List.is_empty !emitted) then raise (no_instance !emitted);
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
      ~on_pred:(fun { Ast.trait; args = [arg] } -> { trait; arg })
      ~on_generic_ty:(fun { type_params; predicates; ty } ->
        { type_params; predicates; ty })
      ~on_tycon:(fun { name; type_params; ty; _ } -> { name; type_params; ty })
      ~on_trait_decl:(fun { name; type_params = [type_param]; methods; _ } ->
        { name; type_param; methods })
      ~on_instance_decl:(fun { Ast.head; type_params; context; methods } ->
        { head; type_params; context; methods })
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
      ~on_prog:(fun { tycons; traits; instances; exp } ->
        (tycons, traits, instances, exp))
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
  let open Singleparam_traits() in
  expect_type "bool" "(fun x -> x) true"

let%test "basic_error" =
  let open Singleparam_traits() in
  expect_raises
    (UnificationFailure "failed to unify type bool -> ?1 with bool")
    "(fun f -> f true) true"

let%test "if" =
  let open Singleparam_traits() in
  expect_type "bool" "if true then false else (fun x -> x) true"

let%test "if_error" =
  let open Singleparam_traits() in
  expect_raises
    (UnificationFailure "failed to unify type bool with ?0 -> ?0")
    "if true then false else fun x -> x"

let%test "let" =
  let open Singleparam_traits() in
  expect_type "bool" "let x = true in if x then false else true"

let%test "let_ann" =
  let open Singleparam_traits() in
  expect_raises
    (TypeError "expression does not have type bool")
    "let x : bool = fun y -> y in x"

let%test "let_rec" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    let rec f = fun x -> if x then g x else x
    and g = fun x -> if x then f x else x in
    f true
  |}

let%test "let_rec_error" =
  let open Singleparam_traits() in
  expect_raises
    (UnificationFailure "failed to unify type bool -> bool with bool")
    {|
      let rec f = fun x -> if x then g x else x
      and g : bool -> bool -> bool = fun x -> if x then f x else x in
      f true
    |}

let%test "tycon_undefined" =
  let open Singleparam_traits() in
  expect_raises
    (Undefined "type Bogus not defined")
    {|
      type Foo = { x : Bogus }
      true
    |}

let%test "record_via_unparameterized_tycon" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    type Foo = { x : bool, y : bool -> bool }
    let foo : Foo = { x = true, y = fun x -> x } in foo.y true
  |}

let%test "row" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    type Foo = { y : bool -> bool }
    let r : Foo = { y = fun x -> x } in (fun s -> s.y) r true
  |}

let%test "row2" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    type Foo = { f : bool -> bool }
    type Bar = { x : bool }
    let r1 : Bar = { x = true } in
    let r2 : Foo = { f = fun x -> x } in
    (fun a -> fun b -> b.f a.x) r1 r2
  |}

let%test "row_if" =
  let open Singleparam_traits() in
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
  let open Singleparam_traits() in
  expect_raises
    (RowMismatch "{y: bool, ...} and {x: bool}")
    {|
      type Foo = { x : bool }
      let foo : Foo = { x = true } in { foo with y = true }
    |}

let%test "let_gen" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    type A = {}
    let a : A = {} in
    let f = fun x -> x in
    let _ = f a in
    f true
  |}

let%test "fix" =
  let open Singleparam_traits() in
  expect_type "bool -> bool" {|
    let rec fix = fun f -> fun x -> f (fix f) x in
    fix (fun f -> fun arg -> if arg then f false else true)
  |}

let%test "let_gen_ann" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    type A = {}
    let a : A = {} in
    let f : forall 'a. 'a -> bool = fun x -> true in
    f a
  |}

let%test "let_gen_error" =
  let open Singleparam_traits() in
  expect_raises
    (TypeError "expression does not have type 'a -> A")
    {|
      type A = {}
      let f : forall 'a. 'a -> A = fun x -> true in
      f true
    |}

let%test "let_gen_scope_error" =
  let open Singleparam_traits() in
  expect_raises
    (UnificationFailure "failed to unify type bool with bool -> ?2")
    "(fun x -> let y = x in y) true true"

let%test "let_typevar_ref" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    let f : forall 'a. 'a -> 'a = fun x -> let y : 'a = x in y in
    f true
  |}

let%test "let_rec_typevar_ref" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    let rec f : forall 'a. 'a -> 'a = fun x -> let y : 'a = x in y in
    f true
  |}

let%test "let_rigid_ok" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    let f : forall 'a. 'a -> 'a = fun x -> x in
    f true
  |}

let%test "let_rigid_error" =
  let open Singleparam_traits() in
  expect_raises
    (TypeError "expression does not have type 'a -> 'b")
    "let f : forall 'a 'b. 'a -> 'b = fun x -> x in f"

let%test "let_rec_rigid_error" =
  let open Singleparam_traits() in
  expect_raises
    (TypeError "expression does not have type 'a -> 'b")
    "let rec f : forall 'a 'b. 'a -> 'b = fun x -> x in f"

let%test "row_ann" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    type Foo = { x : bool, y : bool }
    let get_x : forall 'r. 'r :: { x : bool, ... } => 'r -> bool =
      fun r -> r.x
    in
    let foo : Foo = { x = true, y = false } in
    get_x foo
  |}

let%test "row_ann_missing_field" =
  let open Singleparam_traits() in
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
  let open Singleparam_traits() in
  expect_raises
    (Expected "expected type record, got 'a")
    "let f : forall 'a. 'a -> bool = fun r -> r.x in true"

let%test "let_gen_row" =
  let open Singleparam_traits() in
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
  let open Singleparam_traits() in
  expect_type "bool" {|
    type box 'a = { x : 'a }
    let r : box bool = { x = true } in r.x
  |}

let%test "generic_tycon_let_gen" =
  let open Singleparam_traits() in
  expect_type "box bool" {|
    type box 'a = { x : 'a }
    let identity : forall 'a. box 'a -> box 'a = fun b -> b in
    identity (let r : box bool = { x = true } in r)
  |}

let%test "generic_tycon_error" =
  let open Singleparam_traits() in
  expect_raises
    (RowMismatch "{x: bool} and {x: bool, y: bool}")
    {|
      type box 'a = { x : 'a, y : bool }
      let r : box bool = { x = true } in r.x
    |}

let%test "value_restriction" =
  let open Singleparam_traits() in
  expect_type "Unit" {|
    type Ref 'a = { value : 'a }
    type Unit = {}
    let ref : forall 'a. 'a -> Ref 'a = fun x -> { value = x } in
    let deref : forall 'a. Ref 'a -> 'a = fun r -> r.value in
    let update : forall 'a. Ref 'a -> 'a -> Unit = fun r -> fun x -> {} in
    let r = ref (fun x -> x) in
    let _ = update r (fun x -> if x then false else true) in
    update r (fun x -> false)
  |}

let%test "value_restriction_error" =
  let open Singleparam_traits() in
  expect_raises
    (UnificationFailure "failed to unify type bool with Unit")
    {|
      type Ref 'a = { value : 'a }
      type Unit = {}
      let ref : forall 'a. 'a -> Ref 'a = fun x -> { value = x } in
      let deref : forall 'a. Ref 'a -> 'a = fun r -> r.value in
      let update : forall 'a. Ref 'a -> 'a -> Unit = fun r -> fun x -> {} in
      let r = ref (fun x -> x) in
      let _ = update r (fun x -> if x then false else true) in
      let u : Unit = {} in
      deref r u
    |}

let%test "show_via_base_instance" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    trait Show 'a = { show : 'a -> bool }
    instance Show bool = { show = fun x -> x }
    show true
  |}

let%test "show_no_instance_error" =
  let open Singleparam_traits() in
  expect_raises
    (NoSuchInstance "no instance found for Show bool")
    {|
      trait Show 'a = { show : 'a -> bool }
      show true
    |}

let%test "parameterized_instance" =
  let open Singleparam_traits() in
  expect_type "bool" {|
    type box 'a = { value : 'a }
    trait Show 'a = { show : 'a -> bool }
    instance Show bool = { show = fun x -> x }
    instance forall 'a. Show 'a => Show (box 'a) = { show = fun b -> show b.value }
    let b : box bool = { value = true } in show b
  |}

