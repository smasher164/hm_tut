open Base
open Poly
open Mini_ml

module Five() = struct
  type id = string
  type ty =
    | TyBool (* Bool *)
    | TyArrow of ty * ty (* Function type: T1 -> T2 *)
    | TyVar of tv ref (* Type variable: held behind a mutable reference. *)
    | TyName of id (* Type name: Foo *)
  and record_ty = (id * ty) list
  and row_constraint =
    | NoRow (* No row constraint. *)
    | OpenRow of record_ty (* Must contain at least these fields (from EProj/EWith). *)
    | ClosedRow of record_ty (* Must contain exactly these fields (from ERecord). *)
  and tv = (* A type variable *)
    | Unbound of id * row_constraint
      (* Unbound type variable: Holds the type variable's unique name and any row constraint. *)
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
    | EWith of exp * record_lit (* { r with x = true, y = false} *)
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
    | TEWith of texp * tyrecord_lit * ty
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

  let print_row f row =
    match row with
    | NoRow -> "NoRow"
    | OpenRow flds -> Printf.sprintf "{%s, ...}" (ty_fields f flds)
    | ClosedRow flds -> Printf.sprintf "{%s}" (ty_fields f flds)

  let rec ty_pretty ty =
    match force ty with
    | TyBool -> "bool"
    | TyVar { contents = Link _ } -> failwith "unexpected: Link"
    | TyVar { contents = Unbound(id, NoRow) } -> id
    | TyVar { contents = Unbound(id, (OpenRow _ as row)) } ->
      id ^ print_row ty_pretty row
    | TyVar { contents = Unbound(_, (ClosedRow _ as row)) } ->
      print_row ty_pretty row
    | TyArrow (from, dst) ->
      ty_pretty from ^ " -> " ^ ty_pretty dst
    | TyName name -> name

  let rec ty_debug ty =
    match ty with
    | TyBool -> "TyBool"
    | TyVar { contents = Link ty } ->
        Printf.sprintf "TyVar(Link(%s))" (ty_debug ty)
    | TyVar { contents = Unbound(id, NoRow) } -> Printf.sprintf "TyVar(Unbound %s)" id
    | TyVar { contents = Unbound(id, ((OpenRow _ | ClosedRow _) as row)) } ->
      Printf.sprintf "TyVar(Unbound(%s, %s))" id (print_row ty_debug row)
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
    | TEWith (_, _, ty) -> ty
    | TEProj (_, _, ty) -> ty
    | TELet (_, _, ty) -> ty
    | TELetRec (_, _, ty) -> ty

  (* Global state that stores a counter for generating fresh unbound type variables. *)
  let gensym_counter = ref 0

  (* Generate a fresh unbound type variable. *)
  let fresh_unbound_var ?(row=NoRow) () =
    let n = !gensym_counter in
    Int.incr gensym_counter;
    let tvar = "?" ^ Int.to_string n in
    TyVar (ref (Unbound(tvar, row)))

  let row_iter (row: row_constraint) f =
    match row with
    | NoRow -> ()
    | OpenRow flds | ClosedRow flds -> List.iter flds ~f

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
    | TyVar tgt when phys_equal src tgt -> raise OccursCheck
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
        ignore (union_rows env tv_row (ClosedRow tc.ty))
      | TyVar other when not (phys_equal tv other) ->
        (* Union the rows of these two distinct type variables. *)
        let Unbound(id, other_row) = !other in
        row_iter other_row (fun (_, ty) -> occurs tv ty);
        let row = union_rows env tv_row other_row in
        other := Unbound(id, row)
      | _ when equal tv_row NoRow ->
        (* If either type is a type variable, ensure that the type variable does
           not occur in the type. *)
        occurs tv ty
      | _ ->
        (* ty is not record-like. Can't unify with a row. *)
        raise (unify_failed t1 t2));
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
      (* Variable is being used. Look up its type in the environment. *)
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
        let tc = lookup_tycon tname env in
        (match List.Assoc.find tc.ty ~equal fld with
        | Some ty -> TEProj (rcd, fld, ty)
        | _ -> raise (missing_field fld tc.name))
      | TyVar ({ contents = Unbound(id, row) } as tv) ->
        let fld_ty = fresh_unbound_var () in
        let row = union_rows env row (OpenRow [(fld, fld_ty)]) in
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
  
  (* Walk the typed AST to check for any Unbound type variables, and if found, raise an exception. *)
  let check_no_unbound (texp : texp) : unit =
    let rec ck_ty (ty : ty) : unit =
      match force ty with
      | TyVar { contents = Unbound (id, _) } -> raise (unbound_typevar id)
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

  let typecheck_prog ((tl,exp): prog) : texp =
    let deduped_defs = Hash_set.create (module String) in
    let env = List.map tl ~f:(fun tc ->
      match Hash_set.strict_add deduped_defs tc.name with
      | Ok _ -> (tc.name, TypeBind tc)
      | Error _ -> raise (duplicate_definition tc.name))
    in
    let texp = infer env exp in
    check_no_unbound texp;
    texp

  let convert_prog (ast_prog : Ast.prog) : prog =
    Ast.map_prog
      ~on_ty_bool:(fun () -> TyBool)
      ~on_ty_arrow:(fun a b -> TyArrow (a, b))
      ~on_ty_name:(fun x -> TyName x)
      ~on_generic_ty:(fun _ ty -> ty)
      ~on_tycon:(fun name type_params ty ->
        if not (List.is_empty type_params) then
          failwith "tycon type parameters not supported"
        else { name; ty })
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
  let open Five() in
  expect_type "bool" "(fun x -> x) true"

let%test "basic_error" =
  let open Five() in
  expect_raises
    (UnificationFailure "failed to unify type bool -> ?1 with bool")
    "(fun f -> f true) true"

let%test "if" =
  let open Five() in
  expect_type "bool" "if true then false else (fun x -> x) true"

let%test "if_error" =
  let open Five() in
  expect_raises
    (UnificationFailure "failed to unify type bool with ?0 -> ?0")
    "if true then false else fun x -> x"

let%test "let" =
  let open Five() in
  expect_type "bool" "let x = true in if x then false else true"

let%test "let_ann" =
  let open Five() in
  expect_raises
    (TypeError "expression does not have type bool")
    "let x : bool = fun y -> y in x"

let%test "let_nogen" =
  let open Five() in
  expect_raises
    (UnificationFailure "failed to unify type bool with ?2 -> ?2")
    "let f = fun x -> x in let _ = f true in f (fun y -> y)"

let%test "let_rec" =
  let open Five() in
  expect_type "bool" {|
    let rec f = fun x -> if x then g x else x
    and g = fun x -> if x then f x else x in
    f true
  |}

let%test "let_rec_error" =
  let open Five() in
  expect_raises
    (UnificationFailure "failed to unify type bool -> bool with bool")
    {|
      let rec f = fun x -> if x then g x else x
      and g : bool -> bool -> bool = fun x -> if x then f x else x in
      f true
    |}

let%test "record" =
  let open Five() in
  expect_type "bool" {|
    type Foo = { x : bool, y : bool -> bool }
    let foo : Foo = { x = true, y = fun x -> x } in foo.y true
  |}

let%test "row" =
  let open Five() in
  expect_type "bool" {|
    type Foo = { y : bool -> bool }
    let r : Foo = { y = fun x -> x } in (fun s -> s.y) r true
  |}

let%test "row2" =
  let open Five() in
  expect_type "bool" {|
    type Foo = { f : bool -> bool }
    type Bar = { x : bool }
    let r1 : Bar = { x = true } in
    let r2 : Foo = { f = fun x -> x } in
    (fun a -> fun b -> b.f a.x) r1 r2
  |}

let%test "row_if" =
  let open Five() in
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
  let open Five() in
  expect_raises
    (RowMismatch "{y: bool, ...} and {x: bool}")
    {|
      type Foo = { x : bool }
      let foo : Foo = { x = true } in { foo with y = true }
    |}

let%test "let_rec_record_error" =
  let open Five() in
  expect_raises
    (UnificationFailure "failed to unify type A with bool")
    {|
      type A = {}
      let rec f = fun x -> if x then g x else x
      and g : bool -> A = fun x -> if x then f x else let a : A = {} in a in
      f true
    |}