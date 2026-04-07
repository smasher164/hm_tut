Welcome to part 1 of my tutorial series on type inference!
This post will cover
- The Damas-Hindley-Milner type system
- Unification
- Bidirectional type-checking
- Algorithm J
- Row polymorphism
- Newtype declarations
- Type annotations
- Mutually recursive declarations
- Side-effects / value restriction

We assume you understand
- Abstract Syntax trees
- Vaguely understand what a type system is.

Type inference is the process of taking some expression that represents (part of) a program and returning its type.
If the expression is invalid, i.e. it does some invalid operation according to the rules of your language (like adding a `bool` to a `string`), type inference will fail.
If the expression lacks the sufficient information to return a type, i.e. it is missing a binding in its scope or type information for a binding, type inference will fail.

In this way, type inference is a superset of type-checking. Another term that is used synonymously is type reconstruction.

What type inference is useful for:
- Reducing the number of type annotations you have to write.
- Validating that a program is type-safe, i.e. the program is safe to compile and execute and won't encounter a TypeError.
- Using types to generate code. For example, knowing the types of a struct's fields can help you determine the struct's layout.

Aside: The formal definition of type safety is that "well-typed programs do not get stuck". What this means is if you have an interpreter for a language, and you pass it a program that's been successfully type-checked, it will never reach an unexpected state where it doesn't know how to evaluate something. For example, a multiplication operator in a VM might expect there to be two operands on the stack. Having fewer than two operands would be unexpected.

Different kinds of type systems have different requirements and limitations to type inference.
For instance, subtyping might allow a `List<Square>` to be passed into any function that expects a `List<Rectangle>`. Overloading might require some automatic resolution scheme (based on the number of parameters, types, etc...) to find the correct overload for a function. A borrow checker might want to infer the lifetime of a function parameter based on the lifetime of another. In the case of this article, we'll be covering an ML-like type system.

ML has the unique property of being able to infer the type of an expression in a program without *any* annotations. What's more is that the types it infers for an expression are as general as they can be.

Aside: This is known as the principal type property. If an expression's principal type is P and the expression can also be given the type T, you can always substitute some of the type variables in P to get T.

For most expressions, ML will return types based on the constructors used. For example, an expression like `true && false` would be inferred as `bool`. A lambda like `fun x -> x` when applied to `true` would be given the type `bool -> bool`. However, for `let` bindings, ML will perform a process called *let generalization*. What happens here is that the type of the variable bound by the `let` declaration will be made as polymorphic as possible.

So for example, in
```
let id = fun x -> x
in id true
```
the variable named `id` will be given the type `forall 'a. 'a -> 'a`. For folks more familiar with languages like Java, it'd be like if we declared `id` as
```
T id<T>(T x) {
    return x;
}
```

When `id` gets applied to `true`, its type gets *instantiated* such that `bool` (the type of `true`) can be substituted into it, resulting in a concrete instance of `id` whose type is `bool -> bool`, where the resulting type of the expression `id true` ends up being `bool`.

How do we actually do this process of *generalization* and *instantiation*? How are we able to invoke this generic function without passing in a type argument? How does the type of a function get inferred based on the type of its argument? There are certain rules, known under *Damas-Hindley-Milner* (typically shortened to HM for Hindley-Milner) type inference, that we have to follow to make inferring types like this possible.

The specific implementation of HM we will be covering in this series is called Algorithm J. Another approach to implementing HM is called Algorithm W, but we won't be covering its implementation here, as we'll expand on later. The key difference between Algorithm J and Algorithm W is that the former uses mutable references, while the latter takes a constraint generation/rewriting approach.

We'll start by addressing the question of how we infer the type of a function based on the argument it's applied to. Already, this kind of inference is more powerful than the kind present in languages like Java or Go.

Let's start with our signature for `infer`.
```ocaml
let rec infer (env : env) (exp : exp) : texp = ...
```

`infer` takes an `env` and an `exp` and returns a `texp`.

`env` represents our environment.
```ocaml
type env = (id * bind) list
```
This is where our variable bindings will go during the type-checking process. It will grow as we introduce new bindings.

`id` is just a type alias for string.
```ocaml
(* Represents identifiers like variables, type names, and type variables. *)
type id = string
```
We'll declare `bind` to be a sum type, since we'll introduce other kinds of bindings (like type declarations) later.
```ocaml
type bind =
    | VarBind of ty (* A variable binding maps to a type. *)
```

So for example, if the user wrote
```ocaml
fun x -> foo x
```
the body of the lambda needs to see `x`. In this case, the top of `env` would look like
```
...| "x": Bool |
```

`exp` represents an expression in our program. This is basically our abstract syntax tree (AST). For now, we'll just focus on function application, variables, and booleans.

```ocaml
type exp =
    | EBool of bool (* true/false *)
    | EVar of id (* x *)
    | ELam of id * exp (* fun x -> x *)
    | EApp of exp * exp (* f arg *)
```

`texp` represents a typed expression, a.k.a an expression that holds a `ty`. There's a number of ways a type-checker could choose to define this. You can simply return a type and keep around a map from exp |=> ty. You could parameterize the definition of `exp` so that it can be extended with more variants or fields. In our case, we're going to take a more straightforward approach of defining another typed AST that just duplicates all the variants of our untyped AST.

```ocaml
type texp =
    | TEBool of bool * ty
    | TEVar of id * ty
    | TELam of id * texp * ty
    | TEApp of texp * texp * ty
```
And the types held by `ty` can be
```ocaml
(* A type *)
type ty =
    | TyBool (* Bool *)
    | TyArrow of ty * ty (* Function type: T1 -> T2 *)
    | TyVar of tv ref (* Type variable: held behind a mutable reference. *)
```
We will discuss `tv`'s role shortly.


Here's the expression we're trying to type-check:
```ocaml
(fun x -> x) true
```
As an AST, this looks like
```ocaml
EApp(ELam("x", EVar "x"), EBool true)
```

We'd like to infer types for this expression so that we get
```ocaml
TEApp(TELam("x", TEVar("x", ?0), ?1), TEBool(true, ?2), ?3)
```

where each `?` holds the type for that subexpression.

How do we fill in those holes? To start off, let's try fill in the information we already know.
- The type of `EBool true` should be `TyBool`.
- The return type of the lambda should be the same as its parameter's type, i.e. the type of `x`.
- The parameter type of the lambda should be the same as the type of the lambda's argument, i.e. the type of `EBool true`.
- The type of the application should be the same as the return type of the lambda.

If we wrote these constraints out symbolically, it would look like
```
?2 = TyBool
?1 = TyArrow(?0, ?0)
?1 = TyArrow(?2, ?3)
```

The types represented by a `?` are called type *variables*. If we successfully solve for all of these type variables, we'll have type-checked our program.

The above constraints are basically a system of equations involving types. If you've taken an algebra class, you might recall that one way of solving a system of equations is substitution. That is, you get a variable on its own to one side, and plug the other side in wherever that variable shows up in the other equations. 

So far, our set of solutions contains `{?2 = TyBool}`.

We can start by plugging in `TyBool` wherever we see `?2`. We then get

```
?1 = TyArrow(?0, ?0)
?1 = TyArrow(TyBool, ?3)
```

Now we have two equations set to the same variable. Let's set them equal to each other.
```
TyArrow(?0, ?0) = TyArrow(TyBool, ?3)
```
At this point, we recurse down and solve the corresponding types in the arrow.
```
?0 = TyBool
?0 = ?3
```
We can expand our solution set to `{?2 = TyBool, ?0 = TyBool, ?1 = TyArrow(TyBool, TyBool)}`

Substituting `TyBool` for `?0`, we get
```
TyBool = ?3
```

and our final solution set is `{?2 = TyBool, ?0 = TyBool, ?1 = TyArrow(TyBool, TyBool), ?3 = TyBool}`.

And that's it, we've inferred all the types for this expression.
What does this look like in the failure case?

Let's take the following example:
```ocaml
(fun f -> f true) true
```
As an AST it looks like
```ocaml
EApp(ELam("f", EApp(EVar "f", EBool true)), EBool true)
```
At a glance, we can tell this shouldn't type-check. If evaluated, it's going to try applying a bool like it's a lambda.
Let's generate our type equations to see what happens when we try to solve them. (Since we know that `TEBool` is going to have the type `TyBool`, we don't need an extra equation.)
```ocaml
TEApp(
  TELam("f",
    TEApp(
      TEVar("f", ?0),
      TEBool(true, TyBool),
      ?1
    ),
    ?2,
  ),
  TEBool(true, TyBool),
  ?3
)
```

Let's try to generate type equations for this example. Here's the information we know:
- The parameter type of the lambda is the same as its argument type, a `TyBool`.
- The parameter type of the lambda is the type of `f`.
- The type of the application is the same as the return type of the lambda.
- The parameter type of the lambda needs to be a `TyArrow` to be applied to `true`.
- The return type of the lambda is the return type of `f`.

Writing these constraints out more precisely:
```
?2 = TyArrow(TyBool, ?3)
?2 = TyArrow(?0, ?1)
?0 = TyArrow(TyBool, ?1)
```

To solve this system of equations, we can start by setting the two definitions of `?2` equal to each other.
```
TyArrow(TyBool, ?3) = TyArrow(?0, ?1)
?0 = TyArrow(TyBool, ?1)
```
Now let's substitute `TyArrow(TyBool, ?1)` for every occurence of `?0`.
```
TyArrow(TyBool, ?3) = TyArrow(TyArrow(TyBool, ?1), ?1)
```
Now we start to recurse down both sides and...
```
TyBool = TyArrow(TyBool, ?1)
```
And immediately, we reach a contradiction. `TyBool` is not an arrow type -- it is just `TyBool`.
Since this equation would have to hold in order for this program to type-check, the program does not type-check.

This process of solving equations on types is called *unification*. When we unify two types, we are trying to make them equal to each other by solving any type variables in them. If there's no solution to those type variables such that the two types can be made equal, then like with the previous example, the program will not type-check.

The Algorithm W that was mentioned earlier is just doing unification by building up a solution set, which is substituted in for all the type variables.

However, building up a solution set this way gets a bit unwieldy and slow-performing, since we have to rewrite our entire set of equations every time we want to perform a substitution. That may be fine for visualizing these small examples, but in a large program there can be many thousands of constraints.

We can speed up this substitution process by observing that rewriting the equations is essentially broadcasting to the world the solution to some type variable. And "broadcasting updates to some data" is exactly the problem that mutable references were created to solve. We make each of those type variables a mutable reference, and any equation that mentions that variable automatically sees updates to that type variable. This is the essence of Algorithm J. When we solve that variable, we simply update the type at that reference.

This is what the `tv ref` is meant to be.
```ocaml
(* A type variable *)
type tv =
    | Unbound of id
      (* Unbound type variable: Holds the type variable's unique name. *)
    | Link of ty (* Link type variable: Holds a reference to a type. *)
```
An unsolved type variable is what we consider `Unbound`, as in unbound to any type. It has a unique identifier (like `"?0"`, `"?42"`).

A solved type variable is what we consider "bound". Here, we call it `Link`, as in "linked" to a type. Why "link" and not "bound"? Well you can imagine a type like `ref TyVar(Link (ref TyVar(Link TyBool)))`, i.e. a chain of links that end up at some type. Linking is a convenient way to make a type equal to another one. We simply update its type variable to be a `Link` to the `other_type` like so
```ocaml
tv := Link(other_type)
```

Now let's consider what the implementation of `infer` actually looks like. Given some `exp`, we want to return a `texp` (its typed version). Let's start by matching on the `exp`
```ocaml
let rec infer (env : env) (exp : exp) : texp =
  match exp with
  | EBool b -> ...
  | EVar name -> ...
  | ELam (param, body) -> ...
  | EApp (fn, arg) -> ...
```

We'll take it case-by-case.

The `EBool` case is trivially known, since its type is `TyBool`.
```ocaml
  | EBool b -> TEBool (b, TyBool) (* A true/false value is of type Bool. *)
```

Aside: The typing rule for booleans would look like
```       
        b ∈ {true, false} 
T-Bool:-------------------
           Γ ⊢ b : Bool   
```
This basically says given `b` which is one of `true` or `false`, `b` is of type `Bool` under the typing context `Γ`.

For `EVar`, there is some mention of a variable -- the `x` being passed as an argument to `foo` in `fun x -> foo x`, for example. We want to return the type of that variable. In order to do that, this variable must have already been declared somewhere before this occurence, like as the parameter to a lambda. Because of that, we know it should be in the environment. We just have to search our environment from the innermost scope to outermost for this variable, and grab its type. Let's write that function

```ocaml
(* Lookup a variable's type in the environment. *)
let lookup_var_type name (e : env) : ty =
    match List.Assoc.find e ~equal name with
    | Some (VarBind t) -> t
    | _ -> raise (undefined_error "variable" name)
```

We just call a function from the `List.Assoc` module and search an association list for a `VarBind` that matches `name`.
After invoking this helper on our environment, we get a type associated with the variable name and return it up.

So all in all, the `EVar` case looks like
```ocaml
| EVar name ->
    (* Variable is being used. Look up its type in the environment, *)
    let var_ty = lookup_var_type name env in
    TEVar (name, var_ty)
```

Aside: The typing rule for variables would look like
```
        x:T ∈ Γ  
T-Var:-----------
       Γ ⊢ x : T 
```
This basically says that if `x` is given the type `T` in the context (environment) `Γ`, then we can assume that under the context `Γ`, `x` has the type `T`. Bewildering, I know.

The next case is `ELam`. Given some lambda like `fun param -> body`, we want to return its type, which will be a `TyArrow`. First, we need the type for `param`. If you recall from the example, `param`'s type gets inferred based on the argument of the lambda. What we need to do is associate it with a fresh `Unbound` type variable (call it `ty_param`), so then when the argument's type *is* available, the type variable will get bound to it (they will be unified).

Let's take a look at how `fresh_unbound_var` looks.

`fresh_unbound_var` creates a fresh type variable with a unique id. The unique id is based on an increasing counter variable called `gensym_counter` that gets incremented every time we call this function. We just convert it to a string and make it the basis of the id.

```ocaml
(* Global state that stores a counter for generating fresh unbound type variables. *)
let gensym_counter = ref 0

(* Generate a fresh unbound type variable. *)
let fresh_unbound_var () =
    let n = !gensym_counter in
    Int.incr gensym_counter;
    let tvar = "?" ^ Int.to_string n in
    TyVar (ref (Unbound tvar))
```

After creating a fresh type variable for the `param`, we add an entry to our `env`ironment for the `param` and this type variable. Then we can type-check the body of the lambda with that new environment.
Finally, the resultant type will be the arrow type going from `ty_param` with whatever the type of the lambda's body is. 

So ultimately, the `ELam` case looks like
```ocaml
| ELam (param, body) ->
    (* Instantiate a fresh type variable for the lambda parameter, and
        extend the environment with the param and its type. *)
    let ty_param = fresh_unbound_var () in
    let env' = (param, VarBind ty_param) :: env in
    (* Typecheck the body of the lambda with the extended environment. *)
    let body = infer env' body in
    (* Return a synthesized arrow type from the parameter to the body. *)
    TELam (param, body, TyArrow ( ty_param, typ body ))
```

I'll briefly mention that `typ` just takes a `texp` and return its `ty` field, since we'll sometimes need to grab the `ty` from the result of a recursive call to `infer`.
```ocaml
(* Get the type of a typed expression. *)
let typ (texp : texp) : ty =
  match texp with
  | TEBool _ -> TyBool
  | TEVar (_, ty) -> ty
  | TEApp (_, _, ty) -> ty
  | TELam (_, _, ty) -> ty
```

Aside: The typing rule for lambdas looks like
```
          Γ, x : A ⊢ e : B    
T-Lam:------------------------
       Γ, fun x -> e : A -> B 
```
If under the context `Γ`, `x` (the parameter)'s type being `A` lets us infer that `e` (the body)'s type is `B`, then we can assume that the lambda's type is `A -> B`.

The final case is `EApp`. Given some function `fn` and an argument `arg`, we want to return the type of the result after applying `fn` to `arg`. We'll first want the types of `fn` and `arg`. We can simply call `infer` recursively on `fn` and `arg`, respectively. `fn`'s type should be some `TyArrow(?A, ?B)`. `arg`'s type will be some `?C`.

We know from the discussion on constraints before, that `TyArrow(?A, ?B) = TyArrow(?C, ?D)`, where `?D` is some unbound type variable. `?D` is the type we want to return for this `EApp`.

To accomplish this, we create a fresh unbound type variable to represent `?D`, a.k.a the return type of the `TyArrow`. Then we synthesize a `TyArrow(?C, ?D)` type and unify it with `fn`'s type. This is the first case where unification gets involved. The fresh type variables created by the `ELam` case can get resolved here.

All in all, the final case of `infer`, `EApp`, looks like
```ocaml
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
```

Aside: The typing rules for lambda application look like
```
       Γ ⊢ f : A -> B    Γ ⊢ x : A 
T-App:-----------------------------
               Γ ⊢ f x : B         
```
If under the context `Γ`, `f` (the lambda)'s type is `A -> B` and `x` (the argument)'s type is `A`, then `f x` (`f` applied to `x`)'s type is `B`.

The crux of implementing this case is in how `unify` works, so let's discuss that now.

```ocaml
(* Unify two types. If they are not unifiable, raise an exception. *)
let rec unify (t1 : ty) (t2 : ty) : unit =
    (* Follow all the links. If we see any type variables, they will only be
       Unbound. *)
    let t1, t2 = (force t1, force t2) in
    match (t1, t2) with
    | _ when equal t1 t2 -> ...
    | TyArrow (f1, d1), TyArrow (f2, d2) -> ...
    | TyVar tv, ty | ty, TyVar tv -> ...
    | _ -> ...
```

So to start off, we accept two types that we're going to try to equate.
We `force` them and then match on both. `force` just dereferences all the `Link`s in the a type variable.
```ocaml
let rec force (ty : ty) : ty =
  match ty with
  | TyVar { contents = Link ty } -> force ty
  | ty -> ty
```
Now, we know that if we match on a type variable, that it's definitely `Unbound`, and won't have to do any dereferencing inside the body of `unify`.

Let's take `unify` case-by-case. First, we just try checking if the two types are equal, according to ocaml's definition of equality. Note: we could've explicitly written out this case as `TyBool, TyBool -> ()`, but structural equality handles this for us.
```ocaml
| _ when equal t1 t2 ->
    () (* The types are trivially equal (e.g. TyBool). *)
```

Next, we'll deal with the `TyArrow` case. If both types are `TyArrow`, a.k.a we're trying to equate `TyArrow(A, B) = TyArrow(C, D)`, we should try to `unify A C` and `unify B D`. This corresponds to our example earlier where we recursed down the corresponding types.
```ocaml
| TyArrow (f1, d1), TyArrow (f2, d2) ->
    (* If both types are function types, unify their corresponding types
       with each other. *)
    unify f1 f2;
    unify d1 d2;
```

Finally, we get to the interesting case--when one of the types is a type variable.
You might be wondering why this case is interesting. After all, if one of the types is a type variable, isn't all we have to do just to bind it to the other type, like `tv := Link ty`?

You're right that we have to bind it, but there's also the question of what will happen if we try to unify two types that can form cycles?
Let's trace through the following example and see what happens:
```
unify TyArrow(?0, ?0) TyArrow(TyArrow(TyBool, ?0), ?0)
  unify ?0 TyArrow(TyBool, ?0)
    ?0 := Link(TyArrow(TyBool, ?0))
  unify ?0 ?0
    unify TyArrow(TyBool, ?0) TyArrow(TyBool, ?0)
      unify TyBool TyBool
      unify ?0 ?0 <-- uh-oh! cycle
```

We created a cycle in the first part of the unification (by binding `?0` to `TyArrow(TyBool, ?0)`).
Then the second part of unification (`unify ?0 ?0`) dereferences them and recursively processes the corresponding types in the arrow. When it does that, it eventually hits `unify ?0 ?0` again, resulting in infinite recursion.

This happens because the type pointed to by the type variable `?0` mentions `?0`, a.k.a a cycle. For this reason, before we bind a type variable to another type, we want to ensure that the type variable is not mentioned in that other type.

One might ask, "aren't recursive types useful for things like trees and lists?" They are, but that is a different kind of recursive type than the one we are talking about. A recursive tree like
```ocaml
type tree = 
| Leaf
| Branch of int * tree * tree
```
can always be compared by its name `tree`.

However, with the recursive types we're talking about disallowing, the `tree` type is an infinite structure that needs to be compared while memoizing cycles.

Aside: One can think of cyclic types like these as recursive type aliases or anonymous recursive types. The formal name for these is *equirecursive types*, and they exist in some languages like ocaml with the `-rectypes` flag, and MLScript, which implements algebraic subtyping. A tree type would be expressed as `μT. Leaf | Branch(int, T, T)`. Notice how the recursion is extracted out as the parameter `T`. `μ` is basically a fixed-point combinator for types. When unifying a type variable with another type, we can normalize both types into this `μ` constructor, and then compare them. With nominal types and pattern matching, we explicitly fold and unfold types. This is what's called an *iso-recursive type*.

This process of checking for a cycle before binding a type variable is called an *occurs* check, since we are checking that a type variable does not *occur* in the type we are binding to.

Here is how an occurs check looks. We again match on the forced type, recursively call `occurs` if it's a `TyArrow`, and if we encounter a `TyVar` that's the same reference as the `src`, we have a cycle.
```ocaml
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
```

With that, the `TyVar` case of unification can be written as
```ocaml
| TyVar tv, ty | ty, TyVar tv ->
    (* If either type is a type variable, ensure that the type variable does
       not occur in the type. *)
    occurs tv ty;
    (* Link the type variable to the type. *)
    tv := Link ty
```

Our last case for unification covers any pair of types that don't match the previous cases, and hence don't unify.
```ocaml
| _ ->
    (* Unification has failed. *)
    raise (unify_failed t1 t2)
```

where `unify_failed` is just a helper that constructs an exception that prints out the types that failed to unify:
```ocaml
let unify_failed t1 t2 =
  UnificationFailure
    (Printf.sprintf "failed to unify type %s with %s" (ty_debug t1)
        (ty_debug t2))
```

With that, unification is done and so is our implementation of type inference.
Let's test it out with some examples. In our case, a program is just an expression. We'll define an alias for it, since we'll change this as we add extensions to the language.

```ocaml
type prog = exp
```

# Examples

```ocaml
(* (fun x -> x) true *)
EApp(ELam("x", EVar "x"), EBool true)
```
Output: `bool`

```ocaml
(* (fun f -> f true) true *)
EApp(ELam("f", EApp(EVar "f", EBool true)), EBool true)
```
Output: `UnificationFailure "failed to unify type bool -> ?1 with bool"`

# Simple extensions

Let's extend our language with some simple extensions, namely `if` expressions for branching on a `bool`, nominal type declarations, `let` bindings with type annotations, and mutually recursive `let rec` bindings.

# If expressions

To start, `if` expressions require us to add a new variant to our `exp`
```ocaml
type exp =
    ...
    | EIf of exp * exp * exp (* if <exp> then <exp> else <exp> *)
```
and `texp` types.
```ocaml
type texp =
    ...
    | TEIf of texp * texp * texp * ty
```
as well as update our `typ` helper to extract the `ty` field
```ocaml
let typ (texp : texp) : ty =
  match texp with
  ...
  | TEIf (_, _, _, ty) -> ty
```
In terms of type inference, we only need to add one case to `infer` to handle `EIF`, since we haven't added any new types.
First, we must ensure that the condition is of type `bool`, by calling `infer` on the condition and `unify`ing the resultant type with `TyBool`.
Then, we must ensure that the then branch and else branch have the same types, by calling `infer` on both branches, and `unify`ing their types together.

The resultant type of the `if` can be either one of the types of those branches, since they're the same.

```ocaml
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
```

Aside: The typing rules for `if` expressions are
```
      Γ ⊢ cond : Bool    Γ ⊢ e1 : T    Γ ⊢ e2 : T 
T-If:---------------------------------------------
            Γ ⊢ if cond then e1 else e2 : T       
```
This says if under the context `Γ`, `cond` (the expression in the condition)'s type is `Bool`, `e1` (the expression in the `then` branch)'s type is `T`, and `e2` (the expression in the `else` branch)'s type is `T`, then `if cond then e1 else e2`'s type is `T`.

That was pretty quick! Let's test it out.

# Example

```ocaml
(* if true then false else (fun x -> x) true *)
EIf(EBool true, EBool false, EApp(ELam("x", EVar "x"), EBool true))
```
Output: `bool`

```ocaml
(* if true then false else (fun x -> x) *)
EIf(EBool true, EBool false, ELam("x", EVar "x"))
```
Output: `UnificationFailure "failed to unify type bool with ?0 -> ?0"`

# Type declarations

An example type declaration in this language will be of the form
```
type Foo {
    bar: bool
    baz: bool -> bool
}
```
It can be constructed and projected (selected from) as
```
Foo{bar = true, baz = fun x -> x}.baz
```
A declaration is *nominal*. So another type with the same fields like
```
type Qux {
    bar: bool
    baz: bool -> bool
}
```
cannot be used in place of `Foo`. For example, this program won't type-check:
```
type Box {
    foo: Foo
}
Box{foo = Qux{bar = true, baz = fun x -> x}} (* Type error: expected Foo, got Qux *)
```
Nominal types (or newtypes) are called that because you only need to compare their names to know they are different. And this is how our `unify` will treat them as well.

So let's discuss the implementation of nominal types.
To our expression language, we want to add an `ERecord` variant that constructs the record. It takes the type name and a list of (field,expression) pairs. We also want to add an `EProj` variant that accesses a field of the record with its corresponding name.
```ocaml
type exp =
    ...
    | ERecord of id * record_lit (* Foo{x = true, y = false} *)
    | EProj of exp * id (* r.y *)

and record_lit = (id * exp) list
```
Our `texp` is updated similarly.
```ocaml
type texp =
    ...
    | TERecord of id * tyrecord_lit * ty
    | TEProj of texp * id * ty

and tyrecord_lit = (id * texp) list
```
As expected, we also update the `typ` function to extract the `ty` field from a `TERecord` or `TEProj`.
```ocaml
let typ (texp : texp) : ty =
  match texp with
  ...
  | TERecord (_, _, ty) -> ty
  | TEProj (_, _, ty) -> ty
```

For our types, we need to add two variants--one called `TyRecord` for a record type with its name and all its fields, the other called `TyName` for an arbitrary type name. `TyRecord` will be used to compare field types as well as the type name. For example `Foo{x: bool}` and `Foo{x: bool, y: bool}` are two different types, and wouldn't unify. `TyName` is used for actually mentioning that type anywhere, such as an annotation.

```ocaml
type ty =
    ...
    | TyRecord of id * record_ty (* Record: Foo{x: Bool, y: Bool} *)
    | TyName of id (* Type name: Foo *)

and record_ty = (id * ty) list
```

We also need to add an AST node for the type declarations themselves. We'll modify our `prog` definition to include `tycon list`, which corresponds to type declarations at the top-level which will be accessible to the expressions in the program.

```ocaml
type prog = tycon list * exp
```

As for the definition of `tycon`
```ocaml
(* Type declaration/constructor. All type declarations are nominal records. *)
type tycon = {
    name : id;
    ty : record_ty;
}
```
Those `tycon`s are made available through the `env`ironment, which the type-checker queries. We need to add another variant to `bind` to support types.
```ocaml
type bind =
    ...
    | TypeBind of tycon (* A type binding maps to a type constructor. *)
```

We can go ahead an declare the `lookup_tycon` helper that (similar to `lookup_var_type`) will search the `env` for a `TypeBind` with a name.
```ocaml
(* Lookup a type constructor in the environment. *)
let lookup_tycon name (e : env) : tycon =
  match List.Assoc.find e ~equal name with
  | Some (TypeBind t) -> t
  | _ -> raise (undefined_error "type" name)
```

With that, we can now proceed with the type inference portion.
Let's start by discussing changes to the unification algorithm.

`TyName` is an easy one. If two `TyName`s have the same name, they unify.
```ocaml
| TyName a, TyName b when equal a b -> () (* The type names are the same. *)
```

Great. `TyRecord` is a bit more tedious. Given two record types, for them to unify, we need them to have
- The same type name.
- The same number of fields.
- The same field names.
- The same field types.

We can start off by guarding the match with a comparison of their type names and the length of the fields.
```ocaml
| TyRecord (id1, fds1), TyRecord (id2, fds2)
    when equal id1 id2 && equal (List.length fds1) (List.length fds2) ->
    ...
```
Then we should zip over the fields and unify them. Let's create a helper that unifies two fields.
```ocaml
let unify_fld (id1, ty1) (id2, ty2) =
    if not (equal id1 id2) then raise (unify_failed ty1 ty2)
    else unify env ty1 ty2
in
```
We can use it with `iter2_exn` which is just an ugly name for `zip`.
```ocaml
List.iter2_exn ~f:unify_fld fds1 fds2
```

Overall, the `TyRecord` case looks like this
```ocaml
| TyRecord (id1, fds1), TyRecord (id2, fds2)
    when equal id1 id2 && equal (List.length fds1) (List.length fds2) ->
    (* Both types are records with the same name and number of fields. *)
    let unify_fld (id1, ty1) (id2, ty2) =
        if not (equal id1 id2) then raise (unify_failed ty1 ty2)
        else unify ty1 ty2
    in
    (* Unify their corresponding fields. *)
    List.iter2_exn ~f:unify_fld fds1 fds2
```

We also need to update the `occurs` check to iterate over the types of the fields in a record and check that the `src` type variable does not occur in them.
```ocaml
| TyRecord (_, flds) ->
    (* Check that src occurs in the field types. *)
    List.iter flds ~f:(fun (_, ty) -> occurs src ty)
```

Okay so now that `unify` and `occurs` have been updated, when `infer` calls `unify` on `TyName`s or `TyRecord`s, it will just work.
Now let's update `infer`. We'll start with `ERecord`.

```ocaml
| ERecord (tname, rec_lit) ->
    ...
```

Given a record literal, we need to look up its corresponding type constructor using `tname`.
```ocaml
let tc = lookup_tycon tname env in
```
The type we want to ultimately return is just `TyName tname`. Why not just return `TyRecord`? Well remember that the purpose of nominal types is to be able to compare them by name. Moreover, any of the cases in `infer` can return a type for a record. We need some canonical representation of that type so that we don't end up mixing `TyRecord` and `TyName` during `unify`.

Anyways, before we return `TyName`, we need to turn this type declaration into a `TyRecord`, so we can actually make sure that the record literal the user constructed matches the record type.
```ocaml
let ty_dec = TyRecord(tc.name, tc.ty) in
```
Of course, we can do this with unification. However, what do we unify?
Given the record literal, we should infer a record type from it, and `unify` *that* with the declared type.
We can just iterate over each field and infer its type, synthesizing a `TyRecord` for the whole literal.
```ocaml
let rec_lit = List.map ~f:(fun (id, x) -> (id, infer env x)) rec_lit in
let ty_rec =
    TyRecord (tname, List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit)
in
```
If you're wondering, "why not just call `typ` on the result of `infer` when we first map over the fields?" it's because the `texp` we need to return at the end of inference needs to have the `texp`s for all the fields as well, so we need to keep `rec_lit` around.

Now we can just unify `ty_rec` (the inferred record type) with `ty_dec` (the declared record type).
```ocaml
unify env ty_dec ty_rec;
```
Let's observe, for a moment, that this call to `unify` is comparing an inferred type with a declared type. This pattern will come up again and again in our type-checker. There is a desired type in this scenario, but when `unify` fails, the error message will just be a `UnificationFailure` indicating that they are not the same. Ideally, we show an error message like `"Foo{x = true, y = false} does not have type Foo{x: bool}`, indicating that the record literal does not meet the requirements of the declaration.

To amend this, let's introduce a `check` function that will internally call `unify`, but when it fails, will produce a proper error message. On success, it will return a `texp` (typed expression). We handle `ERecord` as a special case, since this is the helper that `infer` will call to iterate over the record's fields.

```ocaml
let check env ty exp =
    match exp with
    | ERecord (tname, rec_lit) ->
        let rec_lit = List.map ~f:(fun (id, x) -> (id, infer env x)) rec_lit in
        let ty_rec =
            TyRecord (tname, List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit)
        in
        try
            unify ty ty_rec;
            TERecord(tname, rec_lit, ty_rec)
        with UnificationFailure _ ->
            raise (type_error exp ty)
    | exp ->
        let texp = infer env exp in
        try
            unify ty (typ texp);
            texp
        with UnificationFailure _ ->
            raise (type_error exp ty)
```


With `check`, the logic above can be moved, and we can just call `check env ty_dec exp` and unpack the typed fields.

After this part, we can just return the typed record literal.
```ocaml
TERecord (tname, rec_lit, TyName tname)
```

Here is the entire `ERecord` case.
```ocaml
| ERecord (tname, rec_lit) ->
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
```

Note that this pattern of calling a `check` function that internally calls `infer` will come up again and again as long as we have some desired type we want to unify against, e.g. a type annotation. This is actually called *bidirectional type inference*, a fancy name for saying that our type-checker is split between `check` and `infer` which call each other.

Aside: Here are the typing rules for record literals.
```
          T { l_1 : t_1, ..., l_n : t_n } ∈ Δ    Γ ⊢ e_1 : t_1, ..., Γ ⊢ e_n : t_n 
T-Record:--------------------------------------------------------------------------
                         Δ, Γ ⊢ T { l_1 = e_1, ..., l_n = e_n } : T                
```

Note there is another symbol here, `Δ`. `Δ` represents the part of our context containing `TypeBind`s. This rule basically says if there is a type declaration `T` in the type declaration context `Δ`, with the fields `l_1` through `l_n` whose types are `t_1` through `t_n`, and the expressions `e_1` through `e_n` have those respective types, then we can assume that a record constructed like `T { l_1 = e_1, ..., l_n = e_n }` has the type `T`. The `1 ... n` here is the same for the premises and the conclusion, so we are required to have the same number of fields with the same types.

The next case in type inference is `EProj` for projecting onto a record field.
```ocaml
| EProj (rcd, fld) ->
    ...
```
First, we want to infer the type of the expression denoted by `rcd`.
```ocaml
let rcd = infer env rcd in
```
We then need to check that it has the field we're trying to access. The inferred type should be a `TyName` corresponding to the record's type, so we should transform it accordingly.

```ocaml
let (tname, rec_ty) = 
    match typ rcd with
    | TyName tname ->
        let tc = lookup_tycon tname env in
        (tc.name, tc.ty)
    | _ -> raise (expected_ty_error "TyName" (ty_kind ty))
in
```

Now we just have to iterate over `rec_ty` to find `fld`. If we find it, we return that field's type.
Otherwise, raise an error mentioning the field that is missing.
```ocaml
(match List.Assoc.find rec_ty ~equal fld with
| Some ty -> TEProj (rcd, fld, ty)
| _ -> raise (missing_field fld tname))
```

The overall logic for `EProj` looks like
```ocaml
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
```

Aside: The typing rules for record projection look like
```
        Γ ⊢ e : T    T { l_1 : t_1, ..., l_n : t_n } ∈ Δ 
T-Proj:--------------------------------------------------
                       Δ, Γ ⊢ e.l_j : t_j                
```

This basically says if under the context `Γ`, the expression `e` has type `T`, and `T` is some record type declared in the type declaration context `Δ`, then projecting on the record for one of those fields will return the corresponding field's type in the declaration.

Great! Now that we have nominal record construction and projection implemented, let's test some examples.

# Examples

```ocaml
(* type Foo = { x: Bool, y: fun Bool -> Bool }
   Foo{x = true, y = fun x -> x}.y true *)
(
    [{name = "Foo"; ty = [("x", TyBool); ("y", TyArrow(TyBool, TyBool))] }],
    EApp(EProj(ERecord("Foo", [("x", EBool true); ("y", ELam("x", EVar "x"))]), "y"), EBool true)
)
```
Output: `bool`

```ocaml
(* type Foo = { x: Bool, y: fun Bool -> Bool }
   Foo{y = false}.y *)
(
    [{name = "Foo"; ty = [("x", TyBool); ("y", TyArrow(TyBool, TyBool))] }],
    EProj(ERecord("Foo", [("y", EBool false)]), "y")
)
```
Output: `TypeError "expression does not have type Foo{x: bool, y: bool -> bool}"`

# Let bindings

A let binding is an expression like `let x = true in f x` or `let x : bool = true in f x`. Basically, it's a way of binding an identifier (with an optional annotation) to the result of evaluating some expression, and using that binding in the evaluation of another expression. Apart from the optional annotation, `let x = exp in body` is basically sugar for `(fun x -> body) exp`. However, since we want to handle type annotations, and set ourselves up for generalization later on, we will handle this case independently.

To start, we'll need to add an `ELet` variant to our `exp` type. We separate out the binding portion (as `let_decl`) and body portion (as `exp`) for readability and easier destructuring.
```ocaml
type exp =
    ...
    | ELet of let_decl * exp (* let x : <type-annotation> = <exp> in <exp> *)

and let_decl = id * ty option * exp
```

We similarly update our `texp`.
```ocaml
type texp =
    ...
    | TELet of tlet_decl * texp * ty

and tlet_decl = id * ty option * texp
```

Let's look at type inference for our `ELet` case.
```ocaml
| ELet ((id, ann, rhs), body) ->
    ...
```
First, we want to `infer` the type of the right-hand-side of the binding. if there is a type annotation, we want to check that the inferred type unifies with the annotation.

We can use the `check` helper we defined when inferring record types to provide a better error message in case the type of the right-hand-side doesn't match the annotation.

Now we can match against the `ann`otation and `check` that `rhs` satisfies it.
```ocaml
let rhs =
    match ann with
    | Some ann -> check env ann rhs
    | None -> infer env rhs
in
```
We then extend our environment with the binding and its type.
```ocaml
let env = (id, VarBind (typ rhs)) :: env in
```
Finally, we `infer` the body of the binding (the part after the `in`) with the extended environment. This is the type we return up.
```ocaml
let body = infer env body in
TELet ((id, ann, rhs), body, typ body)
```

Our `ELet` case ends up looking like
```ocaml
| ELet ((id, ann, rhs), body) ->
    let rhs =
        match ann with
        | Some ann -> check env ann rhs
        | None -> infer env rhs
    in
    let env = (id, VarBind (typ rhs)) :: env in
    let body = infer env body in
    TELet ((id, ann, rhs), body, typ body)
```

Now let's test it out!

# Examples

```ocaml
(* type A = { x: Bool }
   let r = A{ x = true }
   in r.x *)
(
    [{name = "A"; ty = [("x", TyBool)]}],
    ELet(("r", None, ERecord("A", [("x", EBool true)])), EProj(EVar "r", "x"))
)
```
Output: `bool`

```ocaml
(* type A = {}
   let f = fun x -> x
   in let _ = f A{}
   in f true *)
(
    [{name = "A"; ty = []}],
    ELet(("f", None, ELam("x", EVar "x")),
        ELet(("_", None, EApp(EVar "f", ERecord("A", []))),
        EApp(EVar "f", EBool true)))
)
```
Output: `UnificationFailure "failed to unify type A with bool"`

```ocaml
(* type A = {}
   let x : A = true
   in x *)
(
    [{name = "A"; ty = []}],
    ELet(("x", Some(TyName "A"), EBool true), EVar "x")
)
```
Output: `TypeError "expression does not have type A"`

# (Mutually) recursive definitions

If we wanted to write a recursive `factorial` function or mutually recursive `is_even`/`is_odd` functions, we need to add a `let rec` construct. To make type inference work in this situation, we need `factorial` and `is_even`/`is_odd` in the environments of the function bodies when type-checking them. We also want to make sure there aren't any duplicate definitions.

To start, we'll add an `ELetRec` variant to our `exp` type.
```ocaml
type exp =
    ...
    | ELetRec of let_decl list * exp (* let rec <decls> in <exp> *)
```
We similarly update our `texp`.
```ocaml
type texp =
    ...
    | TELetRec of tlet_decl list * texp * ty
```

Let's take a look at type inference for `ELetRec`.
```ocaml
| ELetRec (decls, body) ->
    ...
```
First, we'd like to extend the environment with all of the declarations in the recursive let binding. We also want to ensure that we don't have any duplicates, so let's initialize a `Hash_set` to store the declaration names.
```ocaml
let deduped_defs = Hash_set.create (module String) in
```
We can map over the declarations, creating a `VarBind` for each one, using annotation if it exists--otherwise just a fresh type variable.
```ocaml
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
```
Next, we use the extended environment to check that the right-hand-side of each let binding matches its corresponding type in the environment.

We zip over the `VarBind` list we created earlier as well as the let declarations themselves, `check`ing that the right-hand-side's type matches the type in the `VarBind`. We return up a `tlet_decl` corresponding to the typed let declaration, ultimately giving us a `tlet_decl list`, which is what's needed in the `TELetRec`.
```ocaml
let decls = List.map2_exn env_decls decls ~f:(
    fun (id, VarBind ty_bind) (_, ann, rhs) ->
        let trhs = check env ty_bind rhs in
        (id, ann, trhs))
in
```

Finally, we `infer` the body of the `let rec` using the extended environment, returning up that type.
```ocaml
let body = infer env body in
TELetRec (decls, body, typ body)
```

Overall, our `ELetRec` case looks like
```ocaml
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
```

That's our `let rec` case! Let's test it out with the `factorial` and `is_even`/`is_odd` examples we mentioned earlier.

# Examples

```ocaml
(* let rec f = fun x -> if x then g x else x
   and g = fun x -> if x then f x else x
   in f true *)
(
    [],
    ELetRec(
        [("f", None, ELam("x", EIf(EVar "x", EApp(EVar "g", EVar "x"), EVar "x")));
        ("g", None, ELam("x", EIf(EVar "x", EApp(EVar "f", EVar "x"), EVar "x")))],
        EApp(EVar "f", EBool true))
)
```
Output: `bool`

```ocaml
(* type A = {}
   let rec f = fun x -> if x then g x else x
   and g = fun x -> if x then f x else A{}
   in f true *)
(
    [{name = "A"; ty = []}],
    ELetRec(
        [("f", None, ELam("x", EIf(EVar "x", EApp(EVar "g", EVar "x"), EVar "x")));
        ("g", None, ELam("x", EIf(EVar "x", EApp(EVar "f", EVar "x"), ERecord("A", []))))],
        EApp(EVar "f", EBool true))
)
```
Output: `UnificationFailure "failed to unify type bool with A"`

# Polymorphism

Up until now, the language we have type-checked does not have any polymorphism.
For example, in the following program, `f` cannot be applied both to `A{}` and to `B{}`.
```
type A = {}
type B = {}

let f = fun x -> x in
let _ = f A{} in
f B{}
```

Our type inference algorithm gives `f` the type `A -> A`, so when it tries to type-check the application to `B`, it fails.

We'd have to rewrite the example to have a separate `fA` and `fB` to get it to type-check.
```
let fA = fun x -> x in
let fB = fun x -> x in
let _ = fA A{} in
fB B{}
```

But when we look at `f`, nothing about its definition requires it to be restricted to `A`. How do we make `f` polymorphic (or generic) over its arguments?

# Instantiation

We'd like `f`'s type to be something like `forall 'a. 'a -> 'a`. But hang on, how would we even use a type like that? We can't exactly unify `'a` with `A`. We need to treat `'a` as a placeholder (or type parameter) that gets substituted with a concrete type argument. This process of taking a generic type and replacing its type parameters with concrete types is called *instantiation*. When `f` gets applied to `A{}` or `B{}`, we look up its type (which will now be generic), and instantiate it to have its type parameters substituted with fresh type variables.

So for example, when `f` is applied to `A{}`, `forall 'a. 'a -> 'a` gets instantiated to get `?0 -> '0`. Then `A -> ?1` gets unified with `?0 -> ?0` as normal, resulting in `A -> A` as the type of the *concrete* instance of `f`.

Likewise, when `f` is applied to `B{}`, `forall 'a. 'a -> 'a` gets instantiated to get `?2 -> '2`, and the same process will result in its concrete type becoming `B -> B`.

To get generic instantiation working, we first want to introduce `generic_ty` that contains a type as well as a list of type parameters.
```ocaml
(* A generic type. Should be read as forall p1..pn. ty, where p1..pn are
    the type parameters. It is separated from ty because in HM, a forall can
    only be at the top level of a type. *)
type generic_ty = {
    type_params: id list;
    ty : ty;
}
```

You might be wondering why `generic_ty` is not just another variant under `ty`, like `Forall of id list * ty`. The short answer is that this kind of polymorphism is not possible in HM, because you no longer get complete type inference and lose principal types. In HM, the type parameters in a generic type are always at the outermost level. So you can have `forall 'a 'b. 'a -> 'b`, but you cannot have `forall 'a. 'a -> forall 'b. 'b`. Supporting the latter would be called *higher-rank polymorphism* (not to be confused with rank polymorphism).

For example, this function can't be written in HM. It accepts a polymorphic identity function as a parameter and instantiates it with two different types.
```
fun f (g: forall a. a -> a) => (g 1, g "hello")
```
However, this is not very limiting in practice. Most of the polymorphic functions you'd ever want to write can be done in HM.

Aside:
There are some useful exceptions though. For example, Haskell can use the `ST` monad to scope an action to a particular thread with the signature
```haskell
runST :: forall a. (forall s. ST s a) -> a
```

Another example is with existentials, like Rust's `dyn` traits or Go's interface values. These can be encoded with higher-rank polymorphism. `exists X. T` (which is roughly like `dyn Trait`) can be written as `forall Y. (forall X. T -> Y) -> Y`. However, this latter feature can be added on its own, and doesn't necessarily need higher-rank polymorphism/polymorphic lambda calculus/System F.

Next, we will update the definition of `VarBind` to hold a `generic_ty` instead of a `ty`. This is needed because, if you consider the example above, `f`'s type in the environment needs to be generic so it can be instantiated. So now `bind` is defined as
```ocaml
type bind =
    | VarBind of generic_ty (* A variable binding maps to a generic type. *)
    | TypeBind of tycon (* A type binding maps to a type constructor. *)
```

Our `lookup_var_type` function should be modified accordingly to return a `generic_ty`.
```ocaml
(* Lookup a variable's type in the environment. *)
let lookup_var_type name (e : env) : generic_ty =
    match List.Assoc.find e ~equal name with
    | Some (VarBind t) -> t
    | _ -> raise (undefined_error "variable" name)
```

We also want to update the type annotations in let bindings to be generic, so if someone were inclined, they could write `let f : forall 'a. 'a -> 'a`.
```ocaml
and let_decl = id * generic_ty option * exp
...
and tlet_decl = id * generic_ty option * texp
```

Now let's discuss the changes to type inference. The first thing that's different is that when we look up a variable in our environment, we get a `generic_ty`. In order to actually use it, we need to instantiate it to turn it into a regular `ty`, where the type parameters are substituted in for fresh type variables.

So in our `EVar` case, after calling `lookup_var_type`, we want to `inst`antiate the `var_ty` before returning it up.
```ocaml
| EVar name ->
    (* Variable is being used. Look up its type in the environment, *)
    let var_ty = lookup_var_type name env in
    (* instantiate its type by replacing all of its quantified type
       variables with fresh unbound type variables.*)
    TEVar (name, inst var_ty)
```

Another place that's different is in type annotations. If you recall from our `ELet` case, when we had an annotation, we called `check env ann rhs`. However, `ann` was a simple type then. Now, it could be generic, so we should instantiate it like `check env (inst ann) rhs`. That's  it! Our `ELet` case now looks like
```ocaml
| ELet ((id, ann, rhs), body) ->
    let rhs =
        match ann with
        | Some ann -> check env (inst ann) rhs
        | None -> infer env rhs
    in
    let env = (id, VarBind (typ rhs)) :: env in
    let body = infer env body in
    TELet ((id, ann, rhs), body, typ body)
```

We update our `ELetRec` case similarly. Where we previously had a
```ocaml
match ann with
| Some ann -> ann
| None -> fresh_unbound_var()
```
We want to `inst ann` in the `Some` case. So our `ELetRec` case should now look like
```ocaml
| ELetRec (decls, body) ->
    let deduped_defs = Hash_set.create (module String) in
    let env_decls = List.map decls ~f:(fun (id, ann, _) ->
        match Hash_set.strict_add deduped_defs id with
        | Ok _ ->
            let ty_decl =
                match ann with
                | Some ann -> inst ann
                | None -> fresh_unbound_var()
            in (id, VarBind ty_decl)
        | Error _ -> raise (duplicate_definition id) 
    ) in
    let env = env_decls @ env in
    let decls = List.map2_exn env_decls decls ~f:(
        fun (id, VarBind ty_bind) (_, ann, rhs) ->
            let trhs = check env ty_bind rhs in
            (id, ann, trhs))
    in
    let body = infer env body in
    TELetRec (decls, body, typ body)
```

Those are the places where we need to instantiate generic types. We should now delve into how `inst` is implemented. Let's run through a simple example first, to get the point across.
Given the generic type `forall a b. a -> (b -> a)`, if `a` had the fresh type variable `?0` and `b` had the fresh type variable `?1`, the instantiated type should be `?0 -> (?1 -> ?0)`.
More concretely, if the `generic_ty` is
```ocaml
{
    type_params = ["a"; "b"];
    ty = TyArrow(TyName "a", TyArrow(TyName "b", TyName "a"))
}
```
the instantiated type is something like
```ocaml
let a = TyVar(ref(Unbound "?0")) in
let b = TyVar(ref(Unbound "?1")) in
TyArrow(a), TyArrow(b, a))
```
(Note: I bound the `TyVar`s to variables here to show that the references would be the same.)

The actual implementation of `inst` just needs to create a mapping from each type parameter to a fresh type variable, traverse over the type, and replace each reference to that type parameter with that type variable.

```ocaml
let inst (gty: generic_ty) : ty =
    ...
```
We'll create a helper to create the mapping as a hash tabe.
```ocaml
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
```

After calling the helper to create the mapping of type parameters to type variables,
```ocaml
let tbl = create_table_for_type_params gty.type_params in
```
we need to walk over `gty.ty` (the underyling type in the generic type) and replace all of the occurences of a type parameter in the hash table with the associated type variable.
Let's create a traversal function `inst'` that accepts and returns a `ty`. We match over a `force ty`, which allows us to compress some of the `Link`s in our types (it's always safe to return the underlying type of a `Link` in place of it).
```ocaml
let rec inst' (ty: ty) =
    match force ty with
    | TyName id as ty ->
    | TyArrow (from, dst) ->
    | TyRecord (id, flds) ->
    | ty -> ty
```
The first case is the most interesting. When we encounter a `TyName` who's `id` is in the hash table, we return the corresponding type variable. Otherwise, just return the type up.
```ocaml
(* The quantified type variable will be referred to by a type name. *)
match Hashtbl.find tbl id with
| Some tv -> tv
| None -> ty
```
For `TyArrow` and `TyRecord`, we just recur over their elements.
```ocaml
| TyArrow (from, dst) ->
    (* Instantiate the type vars in the arrow type. *)
    let from_inst = inst' from in
    let dst_inst = inst' dst in
    TyArrow (from_inst, dst_inst)
```
We'll create a small helper in the `TyRecord` case to `inst`antiate a single field, and we'll use it to map over the record's fields.
```ocaml
| TyRecord (id, flds) ->
    (* Instantiate the type vars in the record fields. *)
    let inst_fld (id, ty) = (id, inst' ty) in
    TyRecord (id, List.map ~f:inst_fld flds)
```
Finally, in any other case, we return up the type as usual, since there's nothing to change.

Our `inst'` helper is called on the generic type's underlying type, a.k.a `gty.ty`. We add a small optimization to avoid calling `inst'` in case there are no type parameters, which avoids unnecessarily traversing the type.
Overall, our `inst` implementation looks like
```ocaml
(* Instantiate a generic type by replacing all the type parameters
   with fresh unbound type variables. Ensure that the same ID gets
   mapped to the same unbound type variable by using an (id, ty) Hashtbl. *)
let inst (gty: generic_ty) : ty =
    let tbl = create_table_for_type_params gty.type_params in
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
        | ty -> ty
    in
    if Hashtbl.is_empty tbl then gty.ty else inst' gty.ty
```

# Generalization

Now that we've covered instantiation of generic types, it's time to get to the meat of Hindley Milner--generalization. Simply put, generalization takes a type that's not generic and makes it generic by turning its unbound type variables into type parameters.

So given a type like
```ocaml
let t = TyVar(ref(Unbound "?0")) in
TyArrow(t, t)
```
generalization could turn it into something like
```ocaml
{
    type_params = ["?0"];
    ty = TyArrow(TyName "?0", TyName "?0")
}
```
I say *could* turn into and not *will* turn into, because there is one crucial piece of information that plays a role in whether a type variable gets generalized--its scope.

The rule is that in a type variable on the right-hand-side of a let binding is only generalized if it was created in the right-hand-side of that let binding. So in other words, for an expression like
```
let x = RHS
in BODY
```
if the type variable's scope is within RHS, it can be generalized.

Now before we talk about how to implement it, let's build up an intuition for why this is.

When a type variable is generalized inside a let binding, it becomes distinct from type variables outside the let binding. This means if that type variable outside the let binding was meant to be resolved into a `bool`, that no longer applies to the generalized type variable.

Let's work through the following example.
```
(fun x -> let y = x in y) true true
```
Already off the bat, we can tell that this program shouldn't type-check. We effectively have an identity function being applied to `true`, and the result is applied to `true`. And we know that `Bool` is not an arrow type, so it can't be applied to anything. (We saw a similar contradiction in an earlier example.)

So what would happen in this example if we generalized *every* type variable on the right-hand-side of a let binding?
If we trace the process of inference, it would look like this
```
 1. (fun x -> let y = x in y) true true              EApp
 2.     (fun x -> let y = x in y) true               EApp
 3.         fun x -> let y = x in y                  ELam
 4.             ty_param = ?0
 5.             env' = ("x", forall _. ?0) :: env
 6.                 let y = x in y                   ELet
 7.                     x                            EVar
 8.                         inst (forall _. ?0)
 9.                         ?0
10.                     ty_gen = gen ?0
11.                     env = ("y", forall ?0. ?0)
12.                     y                            EVar
13.                         inst (forall ?0. ?0)
14.                         ?1
15.                 ?0 -> ?1
16.         true                                     EBool
17.         ty_res = ?2
18.         ty_arr = Bool -> ?2
19.         unify (?0 -> ?1) (Bool -> ?2)
20.         ?2
21.     true                                         EBool
22.     ty_res = ?3
23.     ty_arr = Bool -> ?3
24.     unify ?2 (Bool -> ?3)
25.     ?3
```
On line 4, `x` is given the type variable `?0`.
On line 6, it's bound to `y`.
On line 10, `y`'s type is generalized.
On line 13, it's instantiated to get the type variable `?1`.
On line 15, we see the type of lambda ends up being `?0 -> ?1`.
On line 19, this type is unified with `Bool -> ?2` because of the inner application to `true`.
On line 24, the result type `?2` is unified with `Bool -> ?3` because of the outer application to `true`.

We end up with `?3`, an unbound type var, as the program's type.
But this program should have produced a type error because `Bool` is applied to `Bool`!

The issue is the type of the lambda becoming `?0 -> ?1`. After all, this is an identity function--the type of the lambda should be `?0 -> ?0`. However, generalizing `x`'s type effectively separates it from `?0`, so while `?0` can continue to get unified with `Bool`, that information doesn't get propagated to `?1`.

Because generalization happens at a let binding, we can't allow type variables that are mentioned outside of the let binding to be generalized. That outer type variable and the inner type variable (once instantiated) can end up unifying with different types and diverging, letting you make incorrect assumptions about that type.

In the above example, if we knew that `?0`'s scope escaped outside the let binding, we would not generalize it. The lambda's type would be `?0 -> ?0` and we'd end up trying to unify `Bool` with an arrow type, leading to a type error.

So if our rule is: only generalize type variables inside the scope of the right-hand-side of the let binding, how do we actually track the scope of a type variable?

Since the scope corresponds to the right-hand-side of a let binding, the more nested a let binding is, the deeper its scope. This means we can treat the scope as a positive integer, where a deeper scope (a.k.a a deeper let binding) has a higher number.

Turns out, we just need a single global integer corresponding to the current scope the type-checker is at--we'll call it `current_scope`. When we enter a let binding, we increment its value via `enter_scope`. When we exit the right-hand-side of the let binding, we decrement its value via `leave_scope`.
```ocaml
(* The scope is an integer counter that holds the depth of the current
   let binding. Every unbound type variable contains the scope at which
   it was created. *)
type scope = int

(* Global state that stores the current scope. *)
let current_scope = ref 1
let enter_scope () = Int.incr current_scope
let leave_scope () = Int.decr current_scope
```
Okay we know the current scope, but now we need to associate each type variable with the scope it was created at. We need to modify our definition of `tv` (type variable) to store its scope, as well as modify our `fresh_unbound_var` function to construct a fresh type variable with the current scope.
```ocaml
(* A type variable *)
type tv =
  | Unbound of id * scope
    (* Unbound type variable: Holds the type variable's unique name as well as
       the scope at which it was created. *)
  | Link of ty (* Link type variable: Holds a reference to a type. *)

(* Generate a fresh unbound type variable with a unique name and
   the current scope. *)
let fresh_unbound_var () =
    let n = !gensym_counter in
    Int.incr gensym_counter;
    let tvar = "?" ^ Int.to_string n in
    TyVar (ref (Unbound (tvar, !current_scope)))
```
If the scope of a type variable is greater than the `current_scope`, we know it is deeper (contained inside), and it is safe to generalize. If we take another look at our previous example
```
(fun x -> let y = x in y) true true
```
with the updated generalization logic, we'll see
```
 1. (fun x -> let y = x in y) true true              EApp
 2.     (fun x -> let y = x in y) true               EApp
 3.         fun x -> let y = x in y                  ELam
 4.             ty_param = (?0, 1)                   (scope is 1)
 5.             env' = ("x", forall _. ?0) :: env
 6.                 let y = x in y                   ELet (scope is 2)
 7.                     x                            EVar
 8.                         inst (forall _. ?0)
 9.                         ?0
10.                     ty_gen = gen ?0              1 <= 2
11.                     env = ("y", forall _. ?0)
12.                     y                            EVar
13.                         inst (forall _. ?0)
14.                         ?0
15.                 ?0 -> ?0
16.         true                                     EBool
17.         ty_res = ?1
18.         ty_arr = Bool -> ?1
19.         unify (?0 -> ?0) (Bool -> ?1)
20.         Bool
21.     true                                         EBool
22.     ty_res = ?2
23.     ty_arr = Bool -> ?2
24.     unify Bool (Bool -> ?2)                      TYPE ERROR
```
Note how the generalized type (the type of `y` on line 11) does not have `?0` as a type parameter, since `?0`'s scope (`1`) is not greater than `current_scope` (`2`). When the generalized type gets instantiated, it just returns `?0`, giving the lambda the type `?0 -> ?0`. We see further down that this leads to unifying `Bool` with `Bool -> ?2`, which is a type error, as we expected.

This leads us to ask another question. What happens when a type variable `tv` in an outer scope gets unified with a type `ty` containing type variables in an inner scope? Since we think of unification as equating two types, we should interpret this scenario as `ty` replacing all occurrences of `tv`. This means that all of the type variables inside of `ty` should have the scope of `tv` (a.k.a the outer scope). In implementation terms, this is the minimum of the two scopes.

So what we want is when `unify`ing a `TyVar`  with another type, we traverse the other type for its type variables, and update their scope to be the minimum. If we take a look at our `TyVar` case in `unify`, we already do a traversal of the other type inside of `occurs`. We can take advantage of this and update the scope inside the occurs check.
```ocaml
| TyVar tv, ty | ty, TyVar tv ->
    (* If either type is a type variable, ensure that the type variable does
       not occur in the type. Update the scopes while you're at it. *)
    occurs tv ty;
    (* Link the type variable to the type. *)
    tv := Link ty
```
Then, after the occurs check when we `Link` to the target, the source type variable is automatically updated to point to the target.

Let's look at how we'll modify the `occurs` check. We need to add an additional case.
```ocaml
| TyVar ({ contents = Unbound (id, tgt_scope) } as tgt) ->
    (* Grabbed src and tgt's scopes. *)
    let { contents = Unbound(_, src_scope) } = src in
    (* Compute the minimum of their scopes (the outermost scope). *)
    let min_scope = min src_scope tgt_scope in
    (* Update the tgt's scope to be the minimum. *)
    tgt := Unbound (id, min_scope)
```

Now the overall occurs check looks like
```ocaml
(* Occurs check: check if a type variable (src) occurs in a type (ty).
   If it does, raise an exception. Otherwise, update the scopes of the type variables in ty to be the minimum of its scope and the scope of src. *)
let rec occurs (src : tv ref) (ty : ty) : unit =
    (* Follow all the links. If we see a type variable, it will only be Unbound. *)
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
    | _ -> ()
```

With the occurs check updated, we know that unification will properly ensure that the scope of a type variable gets updated to be the outermost one.

Now let's actually look into how generalization is implemented. `gen` will be a function that accepts a `ty` and returns a `generic_ty`.
```ocaml
let gen (ty: ty) : generic_ty =
    let type_params = Hash_set.create (module String) in
```
We want to walk over the type to find all of its type variables, and grab the `id`s of the ones whose scope is greater than the `current_scope`. We keep track of those ids in a `Hash_set` called `type_params`. Those will be the type parameters in our generalized type.

We create a helper (`gen'`) to recur down the type and return the generalized type. The first case is the only interesting one (the rest are just recurring over the `ty`). If the `scope` of the `Unbound` type variable is greater than `current_scope`, we add the type variable's `id` to the `type_params` hash set, and return up a `TyName` with that `id` to reference that type parameter. (Remember when `inst`antiation comes around, it will look for `TyName`s that correspond to those type parameters.)
```ocaml
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
    | ty -> ty
in
```
Finally, we call `gen'` on the input `ty`, get a sorted list of type parameters from the hash set, and return up our `generic_ty`.
```ocaml
let ty = gen' ty in
let type_params = Hash_set.to_list type_params |> List.sort ~compare in
{ type_params; ty }
```
Overall, our `gen` implementation looks as follows:
```ocaml
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
        | ty -> ty
    in
    let ty = gen' ty in
    let type_params = Hash_set.to_list type_params |> List.sort ~compare in
    { type_params; ty }
```

Since we've finished writing the generalization procedure, let's update our type inference logic in `infer`. Most of our cases will actually not be affected. Just our `ELam`, `ELet`, and `ELetRec` cases.

You might wonder why `ELam` is affected, since we only want to generalize at let bindings. This is correct. We don't want to generalize in `ELam`. However, the bindings in our environment have `generic_ty`. In `ELam`, when we add the `param` to the environment with a fresh type variable, we need to wrap its type inside a `generic_ty`, without actually generalizing it. Let's make a function `dont_generalize` for this purpose.
```ocaml
(* The environment stores generic types, but sometimes, we need to
   associate a non-generalized type to a variable. This function
   wraps a type into a generic type. *)
let dont_generalize ty : generic_ty = { type_params = []; ty }
```
So now, our `ELam` case has to add the binding `(param, VarBind (dont_generalize ty_param))` instead of `(param, VarBind ty_param)`. All in all, it should look like
```ocaml
| ELam (param, body) ->
    (* Instantiate a fresh type variable for the lambda parameter, and
        extend the environment with the param and its type. *)
    let ty_param = fresh_unbound_var () in
    let env' = (param, VarBind (dont_generalize ty_param)) :: env in
    (* Typecheck the body of the lambda with the extended environment. *)
    let body = infer env' body in
    (* Return a synthesized arrow type from the parameter to the body. *)
    TELam (param, body, TyArrow ( ty_param, typ body ))
```
Next, our `ELet` case will be the first interesting one. As mentioned before, we want to `enter_scope()` at its beginning, and `leave_scope()` after inferring the right-hand-side of the binding. The beginning of the case should now look like
```ocaml
| ELet ((id, ann, rhs), body) ->
    enter_scope();
    let rhs =
        match ann with
        | Some ann -> check env (inst ann) rhs
        | None -> infer env rhs
    in
    leave_scope();
    ...
```
On top of this change, however, we want to generalize the type of the right-hand-side.
```ocaml
let ty_gen = gen (typ rhs) in
```
That's the type we add to the environment for the binding.
```ocaml
let env = (id, VarBind ty_gen) :: env in
```
And the rest is kept as usual. Overall, the `ELet` case should look like
```ocaml
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
```
The `ELetRec` case is slightly more complicated. To type-check recursive let bindings, we want to *delay* generalization until after each let binding is inferred. This means that mutually recursive bindings will not be referencing generic versions of each other. Why is this? Turns out, that referencing generic versions of each other while fully inferring their types is undecidable.

Here is an example of polymorphic recursion from the [ocaml docs](https://v2.ocaml.org/manual/polymorphism.html#s%3Apolymorphic-recursion).
```ocaml
type 'a nested =
    | List of 'a list
    | Nested of 'a list nested

let rec depth = function
    | List _ -> 1
    | Nested n -> 1 + depth n
```

Looks like a fairly simple function, but the issue here is that the inner call to `depth n` ends up trying to unify `'a nested` with `'a list nested`, which is not satisfiable. The type checker doesn't realize that the `'a nested` depth was initially called on is different from the `'a list nested` that's the element type. This can be solved by providing an explicit annotation to `depth`, like `forall 'a. 'a nested -> int`. However, there are other issues related to polymorphic recursion in that it can't be monomorphized, and leads to inefficient implementation. In practice, not having polymorphic recursion is not an issue. Most of the recursive functions you'll ever want to define can be written and inferred in this setting.

Aside: The undecidability of type inference for polymorphic recursion was shown by Fritz Henglein in the paper "Type Inference with Polymorphic Recursion". They show that semi-unification reduces to type inference for polymorphic recursion, which implies it's undecidable.

We still want to `enter_scope()` at the beginning, after which we create the `deduped_defs` like before.
```ocaml
| ELetRec (decls, body) ->
    enter_scope();
    let deduped_defs = Hash_set.create (module String) in
```
When we map over each declaration to add its binding to the environment, since we aren't generalizing until later, we just want to add their non-generalized versions to the environment by calling `dont_generalize`. This time, the extended environment is set to a variable named `env'` instead of `env`, because we want to keep the old `env` around so we can add the generalized bindings.
```ocaml
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
```
When we check the right-hand-side of the declarations using the types in the extended environment (`env'`), we call `inst` on it to turn it from a `generic_ty` to `ty`. After all of the right-hand-side expressions in the recursive let binding have been inferred, then we can `leave_scope()`. This list of declarations needs to be a `tlet_decl list`, since that's what `TELetRec` expects.
```ocaml
let decls = List.map2_exn env_decls decls ~f:(
    fun (id, VarBind ty_bind) (_, ann, rhs) ->
        let rhs = check env' (inst ty_bind) rhs in
        (id, ann, rhs))
in
leave_scope();
```
Now we generalize the types of all the bindings by mapping over them and calling `gen` on each one.
```ocaml
let generalized_bindings =
    List.map ~f:(fun (id, _, rhs) -> (id, VarBind (gen (typ rhs)))) decls
in
```
Finally, we add it to the original `env` so we can use it to infer the body of the recursive let binding.
```ocaml
let env = generalized_bindings @ env in
let body = infer env body in
TELetRec (decls, body, typ body)
```

Overall, our updated implementation of `ELetRec` looks like
```ocaml
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
```

Woo! That was a doozy. But we got through it now. How about we take a look at some examples to celebrate?

# Examples

```ocaml
(* type A = {}
   let f = fun x -> x
   in let _ = f A{}
   in f true *)
(
    [{name = "A"; ty = []}],
    ELet(("f", None, ELam("x", EVar "x")),
      ELet(("_", None, EApp(EVar "f", ERecord("A", []))),
        EApp(EVar "f", EBool true)))
)
```
Output: `bool`

```ocaml
(* let rec fix = fun f -> fun x -> f (fix f) x in 
   fix (fun f arg -> if arg then f false else true) *)
(
    [],
    ELetRec([("fix", None, ELam("f", ELam("x", EApp(EApp(EVar "f", EApp(EVar "fix", EVar "f")), EVar "x"))))],
      EApp(EVar "fix", ELam("f", ELam("arg", EIf(EVar "arg", EApp(EVar "f", EBool false), EBool true)))))
)
```
Output: `bool -> bool`

```ocaml
(* type A = {}
   let f : 'a -> bool = fun x -> true
   in f A{} *)
(
    [{name = "A"; ty = []}],
    ELet(("f", Some {type_params = ["'a"]; ty = TyArrow(TyName "'a", TyBool)}, ELam("x", EBool true)),
      EApp(EVar "f", ERecord("A", []))
    )
)
```
Output: `bool`

```ocaml
(* type A = {}
   let f : 'a -> A = fun x -> true
   in f true *)
(
    [{name = "A"; ty = []}],
    ELet(("f", Some {type_params = ["'a"]; ty = TyArrow(TyName "'a", TyName "A")}, ELam("x", EBool true)),
      EApp(EVar "f", EBool true))
)
```
Output: `TypeError "expression does not have type ?1 -> A"`

```ocaml
(* (fun x -> let y = x in y) true true *)
(
    [],
    EApp(EApp(ELam("x", ELet(("y", None, EVar "x"), EVar "y")), EBool true), EBool true)
)
```
Output: `UnificationFailure "failed to unify type bool with bool -> ?2"`

# Generic type declarations

If you notice in our examples above, the type declarations in our examples are not generic. However, in languages like Java or ML, you have access to types like `List` that are instantiated with some type argument. We should extend our language to support these. We already have most of the infrastructure in place, having implemented instantiation. The first thing we'll want to do is modify our definition of `tycon` to contain type parameters.
```ocaml
type tycon = {
    name : id;
    type_params : id list;
    ty : record_ty;
}
```
If you remember with our nominally typed records, we ensured that `ERecord` always returned a `TyName`, and `EProj` grabbed the `TyRecord` given a `TyName` to look for a field. Once we allow type constructors to be generic, we not only have `TyName`s but `TyApp`s (type applications). For example
```
type Box<T> = {
    x: T
}
```
is a type constructor with a single type parameter. For an expression like `Box{x = true}`, we want the inferred type in `ERecord` to be `Box<Bool>`. If there's an `EProj` expression like `Box{x=true}.x`, `EProj` would see a `Box<Bool>`, turn it into a `TyRecord`, and access the `x` field.

To represent types like `Box<Bool>`, we will modify our `ty` definition to add a `TyApp` variant.

```ocaml
type ty =
    ...
    | TyApp of ty list (* Type application: T1 T2 *)
```
A `Box<Bool>` would be represented as `TyApp [TyName "Box"; TyBool]`.

Next, we need to update our `gen`, `unify`, and `occurs` implementations to handle `TyApp`.

In `gen`, we add a case to `gen'` that calls `gen'` on each type in the application, returning the mapped `TyApp`.
```ocaml
| TyApp app ->
    let app = List.map app ~f:gen' in
    TyApp app
```

In `unify`, we add a case where if `t1` and `t2` are `TyApp`s that have the same length, we zip over the application lists and call `unify` on each pair of types.
```ocaml
| TyApp app1, TyApp app2 when List.length app1 = List.length app2 ->
    (* If both types are type applications, unify their corresponding types
       with each other. *)
    List.iter2_exn app1 app2 ~f:unify
```

In `occurs`, we add a case where we iterate over the types in a `TyApp` and check whether `src` occurs in each one.
```ocaml
| TyApp app ->
    (* Check that src occurs in the type application. *)
    List.iter app ~f:(occurs src)
```

Note that we haven't updated `inst`, not because we don't have to, but because `inst` will need some additional changes as we'll see.

Let's consider what we'd have to change in our type inference logic. In the `ERecord` case, after we `lookup_tycon` for the record's type name, we can no longer directly turn the type constructor into a `TyRecord` by creating one with the same name.

The type constructor could have type parameters, in which case we have to instantiate it by creating a `TyApp` with fresh type variables for its arguments.
```ocaml
(* Instantiate the type constructor into a type with fresh unbound
   variables. *)
let ty_app = inst_tycon tc in
```
Then we have to *apply* that `TyApp` to get the `TyRecord`.
```ocaml
(* Apply the type application to get a concrete record type that we can
   unify. *)
let ty_dec = apply_type env ty_app in
```
The type we return up in the `ERecord` case is no longer just a `TyName`, but whatever `ty_app` is, which could be a `TyName` (in case the type constructor has no type parameters) or a `TyApp`.

The `ERecord` case now looks like
```ocaml
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
```
In the `EProj` case, the inferred type of `rcd` could be a `TyApp`, so we should apply its type to its type arguments to get the `TyRecord`.
```ocaml
(* Concretize the type in case it's a type application. *)
let TyRecord(tname, rec_ty) = apply_type env (typ rcd) in
```
The `EProj` case now looks like
```ocaml
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
```

With these cases updated, we should take a look at `inst_tycon` and `apply_type`.

With `inst_tycon` we want to instantiate a `tycon` (type constructor) into a `ty`. If it has no type parameters, then just return its `TyName`. If it *does* have type paramters, map over them to build up a list of fresh unbound type variables for each one, returning a `TyApp` with them as the arguments.
```ocaml
let inst_tycon (tc: tycon) : ty =
    (* No type parameters, so all we need is the type name. *)
    if List.is_empty tc.type_params then TyName tc.name
    else
        (* Map over the type parameters to build up a TyApp with fresh unbound
           variables. *)
        TyApp
            (TyName tc.name
            :: List.map tc.type_params ~f:(fun _ -> fresh_unbound_var ()))
```

`apply_type`, on the other hand, takes either a `TyName` or `TyApp` and returns a `TyRecord`. We need an `env` here, since we'll need to look up the type constructor based on the type name.
```ocaml
let apply_type (env: env) (ty: ty) : ty =
    match ty with
    | TyName id -> ...
    | TyApp (TyName id :: type_args) -> ...
    | _ -> failwith "expected TyName or TyApp"
```
In the `TyName` case, there's nothing to apply, so we just look up the type constructor and return the underlying record type. (This is essentially what our old code for `ERecord`/`EProj` did).
```ocaml
| TyName id ->
    let tc = lookup_tycon id env in
    TyRecord (tc.name, tc.ty)
```
The `TyApp` case is more interesting, and we'll have to modify our `inst` function to make it work. We still look up the type constructor.
```ocaml
| TyApp (TyName id :: type_args) ->
    let tc = lookup_tycon id env in
    ...
```
But this time, we take the `type_params` list in the `tycon`, zip it with `type_args` of the `TyApp` we matched against, and build a hash table associating each type parameter with the corresponding type argument.
```ocaml
let tbl =
    match List.zip tc.type_params type_args with
    | Ok alist -> Hashtbl.of_alist_exn (module String) alist
    | Unequal_lengths ->
        failwith "incorrect number of arguments in type application"
in
```
Finally, and here's the key idea, we build a `generic_ty` with the `type_params` list from the type constructor and a `TyRecord` as its underlying type, and use the `tbl` we built to instantiate it, i.e. substitute occurrences of `type_params` with the `type_args`.
```ocaml
inst ~tbl
    { type_params = tc.type_params; ty = TyRecord (tc.name, tc.ty) }
```
Notice that we are reusing our `inst` function to instantiate this generic type. Calling it will return an instantiated `TyRecord`, which is the result of applying this type.

However, our current definition of `inst` doesn't take a `tbl` argument. Let's change that. Let's go back to our definition of `inst`, and change its signature to
```ocaml
let inst ?(tbl: (id, ty) Hashtbl.t option) (gty: generic_ty) : ty =
```
Here, we've added an optional parameter `tbl`. This means that if a `tbl` is provided, we will use it. Otherwise, construct a table with fresh type variables like we did before with `create_table_for_type_params`.
```ocaml
let tbl =
    (* If a hash table is provided, use it. Otherwise, create a new one. *)
    match tbl with
    | None -> create_table_for_type_params gty.type_params
    | Some tbl -> tbl
in
```
The nice thing here is that none of our calls to `inst` need to be updated, since the argument is optional.

Finally, we need to add one extra case to our `inst'` helper to instantiate the type variables in a type application.
```ocaml
| TyApp app ->
    (* Instantiate the type vars in the type application. *)
    TyApp (List.map app ~f:inst')
```
Overall, our `inst` implementation looks like
```ocaml
let inst ?(tbl: (id, ty) Hashtbl.t option) (gty: generic_ty) : ty =
    let tbl =
        match tbl with
        | None -> create_table_for_type_params gty.type_params
        | Some tbl -> tbl
    in
    let rec inst' (ty: ty) =
        match force ty with
        | TyName id as ty -> (
            match Hashtbl.find tbl id with
            | Some tv -> tv
            | None -> ty)
        | TyArrow (from, dst) ->
            let from_inst = inst' from in
            let dst_inst = inst' dst in
            TyArrow (from_inst, dst_inst)
        | TyRecord (id, flds) ->
            let inst_fld (id, ty) = (id, inst' ty) in
            TyRecord (id, List.map ~f:inst_fld flds)
        | TyApp app ->
            TyApp (List.map app ~f:inst')
        | ty -> ty
    in
    if Hashtbl.is_empty tbl then gty.ty else inst' gty.ty
```

And with `inst` updated, `apply_type` will work, and so will our `ERecord` and `EProj` cases that we updated to handle generic type constructors.

Let's test it out with some examples.

# Examples

```ocaml
(* type box 'a = { x: 'a }
   let r = box{x = true} in r *)
(
    [{name = "box"; type_params = ["'a"]; ty = [("x", TyName "'a")]}],
    ELet(("r", None, ERecord("box", [("x", EBool true)])), EVar "r")
)
```
Output: `box bool`

```ocaml
(* type box 'a = { x: 'a }
  let f = fun v ->
    let r = box{x = box{x = v}}
    in r.x
  in f true *)
(
    [{name = "box"; type_params = ["'a"]; ty = [("x", TyName "'a")]}],
    ELet(("f", None, ELam("v",
      ELet(("r", None, ERecord("box", [("x", ERecord("box", [("x", EVar "v")]))])),
        EProj(EVar "r", "x")))),
      EApp(EVar "f", EBool true))
)
```
Output: `box bool`

```ocaml
(* type box 'a = { x: box 'a, y: bool }
   box{x = true}.x *)
(
    [{name = "box"; type_params = ["'a"]; ty = [("x", TyName "'a"); ("y", TyBool)]}],
    EProj(ERecord("box", [("x", EBool true)]), "x")
)
```
Output: `TypeError "expression does not have type box{x: ?0, y: bool}"`

# Side-effects

Up until now, this language has been pure. You would think adding features like mutability and other side-effects would not be a problem for a polymorphic type system like ours. However, there are gotchas. Let's say we added mutability to our language with a `Ref 'a` type. For example, `Ref int` corresponds to a memory location containing an `int` value. A `Ref 'a` can be built with a `ref` function, whose type is `forall 'a. 'a -> Ref 'a`. You can retrieve the value at a `Ref 'a` via `deref`, whose type is `forall 'a. Ref 'a -> 'a`. A shorthand operator for this is `*r`, where `r` is the name of the reference. Finally, you can update the value at an existing memory location via `update`, whose type is `forall 'a. Ref 'a -> 'a -> ()`. We haven't explicitly mentioned this before, but `()` is the "unit" type. You can think of it like an empty record or tuple. A shorthand syntax for this operation is `*r = v`, where `r` is the name of the reference and `v` is the value being stored.

So for example,
```
let r = ref 0 in
*r = (*r) + 1;
*r
```
this program would create a reference to a memory location containing an integer `0`, increment its contents to be one higher, and then return that value. So far so good. Now let's see what happens when we try to combine references with polymorphism.
```
type A = {}
let r = ref (fun x -> true) in
*r = fun x -> if x then false else true;
(*r) A{}
```
In this example, we create a reference to a lambda and then generalize it. `r` would have the generic type `forall 'a. Ref('a -> bool)`. The third line instantiates the generic type to be `Ref(?0 -> bool)` and unifies `?0 -> bool` with the right-hand-side, whose type is `bool -> bool`. All well and good.

Now comes a problem. The last line again instantiates the generic type to get `Ref(?1 -> bool)`, dereferences it, and applies the lambda to `A{}`. The type-checker accepts this program.

However, if we actually run this, the third line stores a lambda that accepts a `bool`ean condition and does `if condition then ...` to it. And the fourth line invokes that lambda on a value of type `A`. But `A` is not a `bool`!

What we learn from this example is that by generalizing a variable that is mutable, each instantiation gets to ignore changes to the type that other updates made to that memory location. We don't want that, because it means our program is not type-safe! In other words, the evaluator of this language would reach an invalid state at runtime when it tries to do `if A{} then ...`, since `A` is not `bool`.

What can we do about this? The immediate answer is to not generalize expressions like `ref <exp>`, so we just end up with `r`'s type as `Ref(?0 -> bool)`. Then when the third line updates the location to hold `bool -> bool`, that information gets carried into the last line, where we try to unify `bool -> bool` with `A -> ?1` and fail.

Well our intuition is mostly correct, but turns out we need to ensure that expressions we generalize don't contain `ref <exp>` *anywhere* in their body. In our case, we can safely generalize *any* expression that is a constant (`EBool`), variable (`EVar`), lambda (`ELam`), or a record literal (`ERecord`) whose elements are all generalizable. Everything else, like a function application, if expression, record projection, or let binding, we won't generalize.

This is called the *syntactic* value restriction. It is the criterion Standard ML uses to handle mutability. We are basically ensuring that we only generalize *values*, but take a conservative approach and define value as any constant, variable, lambda, or record literal whose elements are all values.

There are other approaches here, including OCaml's that does a deeper syntactic check to allow nested let bindings, record projection, some lambda applications, etc... Other approaches incude changing our evaluation model from eager to lazy, analyzing the bodies of functions being applied to see if there are observable side effects, using an effect system to track effects of expressions, etc... That last one (which Koka employs) is kind of the ultimate solution to the problem, because we get precise tracking at the type-level for expressions that don't perform side effects and can be generalized. However, discussing effect systems is outside the scope of this article, and restricting generalization to syntactic values turns out to not be a problem in practice.

Let's take a look at how we can modify `infer` to implement the value restriction.
We'll start with the `ELet` case. Where we previously just called `gen` on the type of the `rhs`, we now insert a check to see if the `rhs` is syntactically a value.

```ocaml
let ty_gen = if is_value rhs
    then gen (typ rhs)
    else dont_generalize (typ rhs) 
in
```

Now let's write the `is_value` function to determine if an expression is syntactically a value.
```ocaml
let rec is_value (x: texp) : bool =
    match x with
    | TEBool _ | TEVar _ | TELam _ -> true
    | TERecord (_, rec_lit, _) -> List.for_all rec_lit ~f:(fun (_, fld) -> is_value fld)
    | TEApp _ | TEIf _ | TEProj _ | TELet _ | TELetRec _ -> false
```
As you can see, the only complicated case is `TERecord` where we check that all of its fields are also values.

Similarly, we update our `ELetRec` case. Where we previously mapped over the bindings to generalize them, we just check if their right-hand-side is syntactically a value.
```ocaml
let generalized_bindings =
    List.map ~f:(fun (id, _, rhs) ->
        let ty_gen = if is_value rhs
            then gen (typ rhs)
            else dont_generalize (typ rhs) 
        in (id, VarBind ty_gen)) decls
in
```

Putting this all together, we have implemented the value restriction. If we added `ref`, `deref`, and `update` built-ins, our language would correctly handle mutability.

# Example

We can simulate the example from before with our type-checker. We just need to add definitions and signatures for `Ref`, `ref`, `deref`, and `update`. We won't really be able to implement `update` without an actual memory store, so we can just return `Unit` for now. Notice that in order to access a field from the generic struct `Ref 'a`, we add a nested let binding with `forall 'a. Ref 'a` as its annotation. This is needed so `r.value` has access to `r`'s type in the `EProj` case of `infer`.

The actual AST for this example is quite gnarly, but be happy you didn't have to write it! :)
```ocaml
(* type Ref 'a = {
       value: 'a
   }
   type Unit = {}
   let ref = fun x -> Ref { value = x } in
   let deref = fun r ->
       let r : forall 'a. Ref 'a = r
       in r.value
   in
   let update : forall 'a. Ref 'a -> 'a -> Unit = fun r -> fun x -> Unit{}
   let r = ref (fun x -> true) in
   let _ = update r (fun x -> if x then false else true) in
   (deref r) Unit{}
*)

(
    [
      {name = "Ref"; type_params = ["'a"]; ty = [("value", TyName "'a")]};
      {name = "Unit"; type_params = []; ty = []}
    ],
    ELet(("ref", None, ELam("x", ERecord("Ref", [("value", EVar "x")]))),
    ELet(("deref", None, ELam("r", 
      ELet(("r", 
        Some { type_params = ["'a"]; ty = TyApp[TyName "Ref"; TyName "'a"] },
        EVar "r"),
      EProj(EVar "r", "value")))),
    ELet(("update", Some {type_params = ["'a"]; ty =
      TyArrow(
        TyApp[TyName "Ref"; TyName "'a"],
        TyArrow(TyName "'a", TyName "Unit"))},
      ELam("r", ELam("x", ERecord("Unit", [])))),
    ELet(("r", None, EApp(EVar "ref", ELam("x", EBool true))),
    ELet(("_", None, EApp(EApp(EVar "update", EVar "r"),
      ELam("x", EIf(EVar "x", EBool false, EBool true)))),
    EApp(EApp(EVar "deref", EVar "r"), ERecord("Unit", [])))))))
)
```

Similarly, here is how it looks being used successfully.
```ocaml
(* type Ref 'a = {
       value: 'a
   }
   type Unit = {}
   let ref = fun x -> Ref { value = x } in
   let deref = fun r ->
       let r : forall 'a. Ref 'a = r
       in r.value
   in
   let update : forall 'a. Ref 'a -> 'a -> Unit = fun r -> fun x -> Unit{}
   let r = ref (fun x -> true) in
   let _ = update r (fun x -> if x then false else true) in
   update r (fun x -> false)
*)

(
    [
      {name = "Ref"; type_params = ["'a"]; ty = [("value", TyName "'a")]};
      {name = "Unit"; type_params = []; ty = []}
    ],
    ELet(("ref", None, ELam("x", ERecord("Ref", [("value", EVar "x")]))),
    ELet(("deref", None, ELam("r", 
      ELet(("r", 
        Some { type_params = ["'a"]; ty = TyApp[TyName "Ref"; TyName "'a"] },
        EVar "r"),
      EProj(EVar "r", "value")))),
    ELet(("update", Some {type_params = ["'a"]; ty =
      TyArrow(
        TyApp[TyName "Ref"; TyName "'a"],
        TyArrow(TyName "'a", TyName "Unit"))},
      ELam("r", ELam("x", ERecord("Unit", [])))),
    ELet(("r", None, EApp(EVar "ref", ELam("x", EBool true))),
    ELet(("_", None, EApp(EApp(EVar "update", EVar "r"),
      ELam("x", EIf(EVar "x", EBool false, EBool true)))),
    EApp(EApp(EVar "update", EVar "r"), ELam("x", EBool false)))))))
)
```