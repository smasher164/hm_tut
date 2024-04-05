open Base
open Poly

module One () = struct
  type id = string
  type ty =
    | TyBool (* Bool *)
    | TyArrow of ty * ty (* Function type: T1 -> T2 *)
    | TyVar of tv ref (* Type variable: held behind a mutable reference. *)
  and tv = (* A type variable *)
    | Unbound of id
      (* Unbound type variable: Holds the type variable's unique name. *)
    | Link of ty (* Link type variable: Holds a reference to a type. *)
  type bind =
    | VarBind of ty (* A variable binding maps to a type. *)
  type env = (id * bind) list
  type exp =
    | EBool of bool (* true/false *)
    | EVar of id (* x *)
    | ELam of id * exp (* fun x -> x *)
    | EApp of exp * exp (* f arg *)
  type texp =
    | TEBool of bool * ty
    | TEVar of id * ty
    | TELam of id * texp * ty
    | TEApp of texp * texp * ty
  type prog = exp

  let rec force (ty : ty) : ty =
    match ty with
    | TyVar { contents = Link ty } -> force ty
    | ty -> ty

  let rec ty_pretty ty =
    match force ty with
    | TyBool -> "bool"
    | TyVar { contents = Link _ } -> failwith "unexpected: Link"
    | TyVar { contents = Unbound id } -> id
    | TyArrow (from, dst) ->
      "(" ^ ty_pretty from ^ " -> " ^ ty_pretty dst ^ ")"
  
  let rec ty_debug ty =
    match ty with
    | TyBool -> "TyBool"
    | TyVar { contents = Link ty } ->
        Printf.sprintf "TyVar(Link(%s))" (ty_debug ty)
    | TyVar { contents = Unbound id } ->
        Printf.sprintf "TyVar(Unbound %s)" id
    | TyArrow(from, dst) ->
      "(" ^ ty_debug from ^ " -> " ^ ty_debug dst ^ ")"
  
  exception Undefined of string
  exception UnificationFailure of string
  exception OccursCheck

  let undefined_error kind name =
      Undefined (Printf.sprintf "%s %s not defined" kind name)

  let unify_failed t1 t2 =
    UnificationFailure
      (Printf.sprintf "failed to unify type %s with %s" (ty_debug t1)
          (ty_debug t2))

  (* Lookup a variable's type in the environment. *)
  let lookup_var_type name (e : env) : ty =
    match List.Assoc.find e ~equal name with
    | Some (VarBind t) -> t
    | _ -> raise (undefined_error "variable" name)

  (* Get the type of a typed expression. *)
  let typ (texp : texp) : ty =
    match texp with
    | TEBool _ -> TyBool
    | TEVar (_, ty) -> ty
    | TEApp (_, _, ty) -> ty
    | TELam (_, _, ty) -> ty

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
    | _ ->
      (* Unification has failed. *)
      raise (unify_failed t1 t2)

  let rec infer (env : env) (exp : exp) : texp =
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
  
  let typecheck_prog (prog: prog) : texp = infer [] prog
end

let%test "foo" =
  let open One() in
  let prog = EApp(ELam("x", EVar "x"), EBool true) in
  let x = typecheck_prog prog in
  let t = typ x in
  Stdio.print_endline (ty_pretty t);
  Poly.equal (ty_pretty t) "bool"