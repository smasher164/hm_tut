# Type Inference (Part 1)

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
- Have some familiarity with reading OCaml.

All the code in this article can be found in the companion repository https://github.com/smasher164/hm_tut. Each file under the lib directory corresponds to the features added in each section of this article.

Type inference is the process of taking some expression that represents (part of) a program and returning its type.

If the expression is invalid, i.e. it does some invalid operation according to the rules of your language (like adding a `bool` to a `string`), type inference will fail.

If the expression lacks the sufficient information to return a type, i.e. it is missing a binding in its scope or type information for a binding, type inference will fail.

In this way, type inference is a superset of type-checking. Another term that is used synonymously is type reconstruction.

What type inference is useful for:
- Reducing the number of type annotations you have to write.
- Validating that a program is type-safe, i.e. the program is safe to compile and execute and won't encounter a TypeError.
- Using types to generate code. For example, knowing the types of a struct's fields can help you determine the struct's layout.

> Aside: The formal definition of type safety is that "well-typed programs do not get stuck". What this means is if you have an interpreter for a language, and you pass it a program that's been successfully type-checked, it will never reach an unexpected state where it doesn't know how to evaluate something. For example, a multiplication operator in a VM might expect there to be two operands on the stack. Having fewer than two operands would be unexpected.

Different kinds of type systems have different requirements and limitations to type inference.

For instance, subtyping might allow a `List<Square>` to be passed into any function that expects a `List<Rectangle>`. Overloading might require some automatic resolution scheme (based on the number of parameters, types, etc...) to find the correct overload for a function. A borrow checker might want to infer the lifetime of a function parameter based on the lifetime of another. In the case of this article, we'll be covering an ML-like type system.

ML has the unique property of being able to infer the type of an expression in a program without *any* annotations. What's more is that the types it infers for an expression are as general as they can be.

> Aside: This is known as the principal type property. If an expression's principal type is P and the expression can also be given the type T, you can always substitute some of the type variables in P to get T.

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
`infer` takes the environment in the form of an `env` and an expression in the form of an `exp`, returning a typed expression in the form of `texp`.
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

`texp` represents a typed expression, a.k.a an expression that holds a `ty`. There's a number of ways a type-checker could choose to define this. You can simply return a type and keep around a map from `exp |=> ty`. You could parameterize the definition of `exp` so that it can be extended with more variants or fields. In our case, we're going to take a more straightforward approach of defining another typed AST that just duplicates all the variants of our untyped AST.

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

## Unification

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

How do we fill in those holes? To start off, let's try and fill in the information we already know.
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
Now let's substitute `TyArrow(TyBool, ?1)` for every occurrence of `?0`.
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

### Try unification

Here's a small tool for visualizing the process of unification. Enter a few constraints of the form `T1 = T2` (one per line), then click Step to watch each one break down and link type variables to their solutions.

<!-- widget: unification-stepper -->

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

> Aside: The formation rule for booleans looks like
> ```
>         
> WF-Bool:-------------
>          ⊢ Bool type 
> ```
> This is basically an axiom that says `Bool` is a known type.
> 
> The typing rule for booleans would look like
> ```       
>         b ∈ {true, false} 
> T-Bool:-------------------
>            Γ ⊢ b : Bool   
> ```
> This basically says given `b` which is one of `true` or `false`, `b` is of type `Bool` under the typing context `Γ`.

For `EVar`, there is some mention of a variable -- the `x` being passed as an argument to `foo` in `fun x -> foo x`, for example. We want to return the type of that variable. In order to do that, this variable must have already been declared somewhere before this occurrence, like as the parameter to a lambda. Because of that, we know it should be in the environment. We just have to search our environment from the innermost scope to outermost for this variable, and grab its type. Let's write that function

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

> Aside: The typing rule for variables would look like
> ```
>        VarBind(x, T) ∈ Γ 
> T-Var:-------------------
>            Γ ⊢ x : T     
> ```
> This basically says that if `x` has a binding to the type `T` inside the context (environment) `Γ`, then we can assume that under the context `Γ`, `x` has the type `T`. Bewildering, I know.

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

I'll briefly mention that `typ` just takes a `texp` and returns its `ty` field, since we'll sometimes need to grab the `ty` from the result of a recursive call to `infer`.
```ocaml
(* Get the type of a typed expression. *)
let typ (texp : texp) : ty =
  match texp with
  | TEBool _ -> TyBool
  | TEVar (_, ty) -> ty
  | TEApp (_, _, ty) -> ty
  | TELam (_, _, ty) -> ty
```

> Aside: The formation rule for function types looks like
> ```
>           ⊢ A type    ⊢ B type 
> WF-Arrow:----------------------
>               ⊢ A -> B type    
> ```
> This says that if `A` and `B` are types, then `A -> B` is a type.
> 
> The typing rule for lambdas looks like
> ```
>        Γ, VarBind(x, A) ⊢ e : B 
> T-Lam:--------------------------
>         Γ ⊢ fun x -> e : A -> B 
> ```
> If under the context `Γ`, `x` (the parameter)'s type being `A` lets us infer that `e` (the body)'s type is `B`, then we can assume that the lambda's type is `A -> B`.

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

> Aside: The typing rules for lambda application look like
> ```
>        Γ ⊢ f : A -> B    Γ ⊢ x : A 
> T-App:-----------------------------
>                Γ ⊢ f x : B         
> ```
> If under the context `Γ`, `f` (the lambda)'s type is `A -> B` and `x` (the argument)'s type is `A`, then `f x` (`f` applied to `x`)'s type is `B`.

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
We `force` them and then match on both. `force` just dereferences all the `Link`s in a type variable.
```ocaml
let rec force (ty : ty) : ty =
  match ty with
  | TyVar { contents = Link ty } -> force ty
  | ty -> ty
```
Now, we know that if we match on a type variable, that it's definitely `Unbound`, and won't have to do any dereferencing inside the body of `unify`.

Let's take `unify` case-by-case. First, we just try checking if the two types are equal, according to OCaml's definition of equality. Note: we could've explicitly written out this case as `TyBool, TyBool -> ()`, but structural equality handles this for us.
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

> Aside: One can think of cyclic types like these as recursive type aliases or anonymous recursive types. The formal name for these is *equirecursive types*, and they exist in some languages like OCaml with the `-rectypes` flag, and MLScript, which implements algebraic subtyping. A tree type would be expressed as `μT. Leaf | Branch(int, T, T)`. Notice how the recursion is extracted out as the parameter `T`. `μ` is basically a fixed-point combinator for types. When unifying a type variable with another type, we can normalize both types into this `μ` constructor, and then compare them. With nominal types and pattern matching, we explicitly fold and unfold types. This is what's called an *iso-recursive type*.

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
    (Printf.sprintf "failed to unify type %s with %s" (ty_debug t1) (ty_debug t2))
```

With that, unification is done and so is our implementation of type inference.
Let's test it out with some examples. In our case, a program is just an expression. We'll define an alias for it, since we'll change this as we add extensions to the language.

```ocaml
type prog = exp
```

You can find and run these examples in [lib/one.ml](lib/one.ml).

### Examples

```ocaml
typecheck_prog
    (* (fun x -> x) true *)
    (EApp(ELam("x", EVar "x"), EBool true))
```
Output: `bool`

```ocaml
typecheck_prog
    (* (fun f -> f true) true *)
    (EApp(ELam("f", EApp(EVar "f", EBool true)), EBool true))
```
Output: `UnificationFailure "failed to unify type bool -> ?1 with bool"`

## Simple extensions

Let's extend our language with some simple extensions, namely `if` expressions for branching on a `bool`, `let` bindings with type annotations, mutually recursive `let rec` bindings, and nominal type declarations.

## If expressions

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
In terms of type inference, we only need to add one case to `infer` to handle `EIf`, since we haven't added any new types.
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

> Aside: The typing rules for `if` expressions are
> ```
>       Γ ⊢ cond : Bool    Γ ⊢ e1 : T    Γ ⊢ e2 : T 
> T-If:---------------------------------------------
>             Γ ⊢ if cond then e1 else e2 : T       
> ```
> This says if under the context `Γ`, `cond` (the expression in the condition)'s type is `Bool`, `e1` (the expression in the `then` branch)'s type is `T`, and `e2` (the expression in the `else` branch)'s type is `T`, then `if cond then e1 else e2`'s type is `T`.

That was pretty quick! Let's test it out.

You can find and run these examples in [lib/two.ml](lib/two.ml).

### Examples

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

## Let bindings

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
First, we want to `infer` the type of the right-hand-side of the binding. If there is a type annotation, we want to check that the inferred type unifies with the annotation. This pattern of comparing an inferred type with a declared type will come up again and again in our type-checker. We can extract it out into a helper called `check`.

```ocaml
  let rec check env ty exp =
    let texp = infer env exp in
    (try
        unify ty (typ texp);
        texp
    with UnificationFailure _ ->
        raise (type_error ty))
```

This is actually the *checking mode* of bidirectional type-checking. `infer` is what's called *inference mode* (or sometimes *synthesis mode*): given an expression, we produce its type. `check` is its dual: given an expression *and* an expected type, we verify the expression has that type. We use checking mode when the expected type is known from the context (like an annotation), and inference mode when it isn't.

Now we can match against the annotation and `check` that `rhs` satisfies it.
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

> Aside: Here are the typing rules for `ELet`. We split them into two rules, one for a let binding without an annotation and one for a let binding with an annotation.
> 
> ```
>        Γ ⊢ rhs : A    Γ, VarBind(x, A) ⊢ body : B 
> T-Let:--------------------------------------------
>                Γ ⊢ let x = rhs in body : B        
> ```
> This says that under the context, if `rhs` can be inferred to be the type `A`, and the context extended with `x` having the type `A` lets us give `body` the type `B`, then the entire expression `let x = rhs in body` can be given the type `B`.
> 
> ```
>           ⊢ A type    Γ ⊢ rhs : A    Γ, VarBind(x, A) ⊢ body : B 
> T-LetAnn:--------------------------------------------------------
>                       Γ ⊢ let x : A = rhs in body : B            
> ```
> This says that if `A` is a valid type, `rhs` can be inferred to be the type `A`, and the context extended with `x` annotated with the type `A` lets us give `body` the type `B`, then the entire annotated expression `let x: A = rhs in body` can be given the type `B`.
> 
> Note that the only thing that's really changed here is that we need to make sure that `A` is a well-formed annotation. Other than that, the first rule is deriving `A` and in the second, `A` is an annotation supplied by the programmer.

Now let's test it out!

You can find and run these examples in [lib/three.ml](lib/three.ml).

### Examples

```ocaml
typecheck_prog
    (* let x = true in if x then false else true *)
    (ELet(("x", None, EBool true), EIf(EVar "x", EBool false, EBool true)))
```
Output: `bool`

```ocaml
typecheck_prog
    (* let x : bool = fun y -> y in x *)
    (ELet(("x", Some TyBool, ELam("y", EVar "y")), EVar "x"))
```
Output: `TypeError "expression does not have type bool"`

## (Mutually) recursive definitions

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
First, we'd like to extend the environment with all of the declarations in the recursive let binding. We map over the declarations, creating a `VarBind` for each one, using an annotation if it exists--otherwise just a fresh type variable.
```ocaml
let env_decls = List.map decls ~f:(fun (id, ann, _) ->
    let ty_decl =
        match ann with
        | Some ann -> ann
        | None -> fresh_unbound_var()
    in (id, VarBind ty_decl)
) in
let env = env_decls @ env in
```
Next, we use the extended environment to check that the right-hand-side of each let binding matches its corresponding type in the environment.

We zip over the `VarBind` list we created earlier as well as the let declarations themselves, checking that the right-hand-side's type matches the type in the `VarBind`. We return up a `tlet_decl` corresponding to the typed let declaration, ultimately giving us a `tlet_decl list`, which is what's needed in the `TELetRec`.
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
    let env_decls = List.map decls ~f:(fun (id, ann, _) ->
        let ty_decl =
            match ann with
            | Some ann -> ann
            | None -> fresh_unbound_var()
        in (id, VarBind ty_decl)
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

> Aside: Here's the typing rule for `ELetRec`.
> 
> ```
>           Γ_rec = Γ, { VarBind(x, A_x) | x ∈ decls }    Γ_rec ⊢ rhs_x : A_x for each x ∈ decls    Γ_rec ⊢ body : B 
> T-LetRec:----------------------------------------------------------------------------------------------------------
>                                       Γ ⊢ let rec { x = rhs_x | x ∈ decls } in body : B                            
> ```
> 
> `decls` is the set of names being bound in the let-rec. `A_x` is the type for binding `x` and `rhs_x` is its right-hand-side. `Γ_rec` is the context `Γ` extended with all of the bindings, so each `rhs_x` can refer to any of them. This rule basically says that if each `rhs_x` has the type `A_x` under `Γ_rec`, and the body has the type `B` under `Γ_rec`, then `let rec { x = rhs_x | x ∈ decls } in body` has type `B`.
> 
> For annotated bindings, assuming `A_x` is well-formed, `A_x` comes from its annotation with its quantified type variables made rigid in `Γ_rec`.

That's our `let rec` case! Let's test it out with some examples. At this point, manually writing out the AST is going to get tedious, so I'll just show the source. If you're following along with the repo, you'll notice that we've integrated so that we can avoid writing the AST out by hand.

You can find and run these examples in [lib/four.ml](lib/four.ml).

### Examples

```ocaml
typecheck_source {|
    let rec f = fun x -> if x then g x else x
    and g = fun x -> if x then f x else x
    in f true
|}
```
Output: `bool`

```ocaml
typecheck_source {|
    let rec f = fun x -> if x then g x else x
    and g : bool -> bool -> bool = fun x -> if x then f x else x in
    f true
|}
```
Output: `UnificationFailure "failed to unify type bool -> bool with bool"`

## Type declarations

An example type declaration in this language will be of the form
```
type Foo = {
    bar: bool
    baz: bool -> bool
}
```
Note that the type name corresponds to a record.
It can be constructed and projected (selected from) with
```
let foo : Foo = {bar = true, baz = fun x -> x} in
foo.baz
```
A declaration is *nominal*. So another type with the same fields like
```
type Qux = {
    bar: bool
    baz: bool -> bool
}
```
cannot be used in place of `Foo`. For example, this program won't type-check:
```
let qux : Qux = {bar = true, baz = fun x -> x} in
let foo : Foo = qux (* Type error: expected Foo, got Qux *)
```

Nominal types (or newtypes) are called that because you only need to compare their names to know they are different, and this is how our `unify` will treat them as well. However, if you notice in the previous examples, we construct these records without mentioning the type name on the record literal, i.e. there is no `Foo{...}` form. So while we can compare types by their name to know that they are different, we will still have to infer that a record literal corresponds to some pre-declared type. The secret sauce we need to do that is called *rows*, which we'll describe shortly.

Let's discuss the implementation of our nominal types.
First, let's introduce type declarations (type constructors) to our language.
```ocaml
type tycon = {
    name : id;
    ty : record_ty;
}
and record_ty = (id * ty) list
```
Our `prog` is now more than just an `exp`. Rather, it is now a list of type constructors and an `exp`.
```ocaml
type prog = tycon list * exp
```
We also need a way of referring to a user-defined type by name.
```ocaml
type ty =
    ...
    | TyName of id (* Type name: Foo *)
```
Types get added to the environment just like variables. When we search for and find a type in the environment, we get back a `TypeBind` holding our `tycon`
```ocaml
type bind =
    ...
    | TypeBind of tycon (* A type binding maps to a type constructor. *)
```
At the expression-level, we need a way to construct these records by specifying all of its fields.
```ocaml
type exp =
    ...
    | ERecord of record_lit (* {x = true, y = false} *)
```
We'll add a way to update fields using a `with` expression, producing a record of the same type with the provided fields set to different values
```ocaml
type exp =
    ...
    | EWith of exp * record_lit (* { r with x = true, y = false} *)
```
and a way to access fields (also called projection)
```ocaml
type exp =
    ...
    | EProj of exp * id (* r.y *)
```
where `record_lit` is a list of (field name, expression) pairs
```ocaml
and record_lit = (id * exp) list
```
Correspondingly, we update `texp` and define `tyrecord_lit`
```ocaml
type texp =
    ...
    | TERecord of tyrecord_lit * ty
    | TEWith of texp * tyrecord_lit * ty
    | TEProj of texp * id * ty
and tyrecord_lit = (id * texp) list
```
We can go ahead and declare the `lookup_tycon` helper that (similar to `lookup_var_type`) will search the `env` for a `TypeBind` with a name.
```ocaml
(* Lookup a type constructor in the environment. *)
let lookup_tycon name (e : env) : tycon =
    match List.Assoc.find e ~equal name with
    | Some (TypeBind t) -> t
    | _ -> raise (undefined_error "type" name)
```
Finally, in order to infer that a record literal constructs some predeclared type, we need that secret sauce I mentioned earlier. Remember how unification used type variables in place of types we hadn't figured out yet? We want to use those type variables for records as well, but we also want to say "we haven't figured out the type of this record yet, but we know it should have *these* fields". To do this, we are going to stash a constraint inside our `Unbound` type variable called a `row_constraint`.

Basically, a *row* is a set of (label, type) pairs, a.k.a a set of field names and their types (they can also correspond to variant names and their types, but we will not be covering those in this post). If you recall, `record_ty` is exactly the structure we want to represent such a set. Our constraints, then, are how we indicate that a type variable should have *at least* certain fields or *exactly* certain fields.
```ocaml
and row_constraint =
    | NoRow (* No row constraint. *)
    | OpenRow of record_ty (* Must contain at least these fields (from EProj/EWith). *)
    | ClosedRow of record_ty (* Must contain exactly these fields (from ERecord). *)
```
and so we extend the definition of an `Unbound` type variable to be
```ocaml
and tv = (* A type variable *)
    | Unbound of id * row_constraint
    ...
```
`NoRow` is there to represent a regular type variable as we used it earlier, `OpenRow` is there to say that a type must have at least these fields, and `ClosedRow` says that a type must have exactly these fields. For example, `A::{x: int, ...}` says that the type `A` must be a record type that at least has a field named `x` whose type is `int`. Similarly, `B::{x: int, y: int}` says that the type `B` must be a record type that exactly has the fields `x` and `y` which are both of the type `int`.

During type inference, we will encounter places where given two types that both contain row constraints, we will need to combine them. For this reason, we will define a `union_rows` helper.
```ocaml
let rec union_rows env (row_a: row_constraint) (row_b: row_constraint) : row_constraint =
    match (row_a, row_b) with
    ...
```
If `NoRow` is unioned with something else, that other row is the result.
```ocaml
| NoRow, row | row, NoRow -> row
```
If two `OpenRow`s are unioned together, we want to merge their fields, producing a new `OpenRow`. If they both share fields of the same name, unify their types together.
```ocaml
| OpenRow row_a, OpenRow row_b ->
    OpenRow (List.dedup_and_sort (row_a @ row_b) ~compare:(fun (f1,t1) (f2,t2) ->
    if String.equal f1 f2 then (unify env t1 t2; 0)
    else Poly.compare (f1,t1) (f2,t2)))
```
If an `OpenRow` is unioned with a `ClosedRow`, we return the `ClosedRow`. However, we need to ensure that the fields in the `OpenRow` are a subset of the fields in the `ClosedRow`, since an `OpenRow` says we want *at least* those fields held by its constraint. For this case, we will define a `fld_exists` helper that checks that a field name exists in a `record_ty` and if so, that its type unifies with our expected type.
```ocaml
and fld_exists env (rcd: record_ty) id ty =
    List.exists rcd ~f:(fun (f,t) -> String.equal f id && (unify env t ty; true))
```
Using this, our next case inside `union_rows` is as follows:
```ocaml
| OpenRow o_row, ClosedRow c_row | ClosedRow c_row, OpenRow o_row ->
    List.iter o_row ~f:(fun (id,ty) ->
        if not (fld_exists env c_row id ty) then
            raise (row_mismatch row_a row_b)); ClosedRow c_row
```
Now if two `ClosedRow`s are unioned together, we need to ensure they have the same exact fields. We can first check that their length is the same and then check that each of the first row's fields is present in the second.
```ocaml
| ClosedRow flds1, ClosedRow flds2 when Int.equal (List.length flds1) (List.length flds2) ->
    List.iter flds1 ~f:(fun (id,ty) ->
        if not (fld_exists env flds2 id ty) then
            raise (row_mismatch row_a row_b)); ClosedRow flds1
```
Finally, in any other case, we can say that the rows don't match. We raise a `RowMismatch` exception.
```ocaml
| _ -> raise (row_mismatch row_a row_b)
```

Let's see how these constraints come up during type inference.

We'll start off by extending `infer` to handle the record literal `ERecord`. Off the bat, even though we don't currently know the name of its type, we know exactly the fields it must have, so it must be a `ClosedRow` of some kind. Also, to know the type of a record, we need to know the type of each of its fields, so we should call `infer` on each field's type.
```ocaml
| ERecord rec_lit ->
    let rec_lit = List.map rec_lit ~f:(fun (id, x) -> (id, infer env x)) in
```
We get back a `tyrecord_lit`. Since we want to return up its type, we want to map over and get the name and type of each field to get our `record_ty`.
```ocaml
    let flds = List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit in
```
Finally, to represent the type we'll return up, we create an `Unbound` type variable with a `ClosedRow` constraint holding `flds`.
```ocaml
fresh_unbound_var ~row:(ClosedRow flds) ()
```
Overall, our `ERecord` case of `infer` will look like this:
```ocaml
| ERecord rec_lit ->
    let rec_lit = List.map rec_lit ~f:(fun (id, x) -> (id, infer env x)) in
    let flds = List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit in
    TERecord (rec_lit, fresh_unbound_var ~row:(ClosedRow flds) ())
```
The next expression we have to typecheck is `EWith`, which is of the form `{ r with x = true }`. Basically, given some record and some fields that are being assigned, we need to ensure that the record has at least the fields that are being assigned. That is, the type we return for an `EWith(rcd, flds)` expression is an `Unbound` type variable with an `OpenRow` constraint holding the types of `flds`.

We start by inferring the type of the record.
```ocaml
| EWith (rcd, flds) ->
    let rcd = infer env rcd in
```
And like before, we want to map over the `flds` and infer the type of each one of them, followed by mapping over the `tyrecord_lit` to get a `record_ty`.
```ocaml
let rec_lit = List.map flds ~f:(fun (id, x) -> (id, infer env x)) in
let flds = List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit in
```
We can now generate an `Unbound` type variable for the return type holding the `OpenRow` constraint.
```ocaml
let row = fresh_unbound_var ~row:(OpenRow flds) () in
```
We want to ensure that the type of `rcd` is equivalent to `row`, since `EWith` guarantees that the input and the output type are the same. This is why we'll unify them.
```ocaml
unify env (typ rcd) row;
```
We can then return the `TEWith` up with the typed record, fields, and unified type. Overall, our `EWith` case should look like this:
```ocaml
| EWith (rcd, flds) ->
    let rcd = infer env rcd in
    let rec_lit = List.map flds ~f:(fun (id, x) -> (id, infer env x)) in
    let flds = List.map ~f:(fun (id, x) -> (id, typ x)) rec_lit in
    let row = fresh_unbound_var ~row:(OpenRow flds) () in
    unify env (typ rcd) row;
    TEWith (rcd, rec_lit, typ rcd)
```
The last expression we need to infer the type of is `EProj`, which involves accessing a field from a record. We follow a similar approach here. Given an `EProj(rcd, fld)`, we synthesize an `Unbound` type variable with an `OpenRow` constraint containing `fld` and its type, unifying the type variable with the type of `rcd`.
```ocaml
| EProj (rcd, fld) ->
    let rcd = infer env rcd in
    let fld_ty = fresh_unbound_var () in
    let row = fresh_unbound_var ~row:(OpenRow [(fld, fld_ty)]) () in
    unify env (typ rcd) row;
    TEProj (rcd, fld, fld_ty)
```
Those are all the changes to `infer`. We need to now update `unify` to handle type names and row constraints.

The bulk of the new logic happens when we try to unify `TyVar` with some other type. Since `TyVar` can now hold a `row_constraint`, if the other type is record-shaped, we need to combine the constraints of both types.

We start off by destructuring the type variable.
```ocaml
and unify env (t1 : ty) (t2 : ty) : unit =
    ...
    | TyVar tv, ty | ty, TyVar tv ->
        let Unbound(_, tv_row) = !tv in
```
We then want to match against `ty` and depending on what it is, union its rows with `tv_row`.

First, if `ty` is a `TyName`, we want to look up that type name in the environment, get its underlying record, and union its rows with `tv_row`.
```ocaml
match ty with
| TyName tname ->
    let tc = lookup_tycon tname env in
    ignore (union_rows env tv_row (ClosedRow tc.ty))
...
```
Next we handle the case where `ty` is a type variable that is distinct from `tv`.
```ocaml
| TyVar other when not (phys_equal tv other) ->
    let Unbound(id, other_row) = !other in
```
We will union `tv_row` with `other_row`. Let's define a helper `row_iter` that walks the fields in a `row_constraint`.
```ocaml
let row_iter (row : row_constraint) f =
  match row with
  | NoRow -> ()
  | OpenRow flds | ClosedRow flds -> List.iter flds ~f
```
First, we should make sure `tv` isn't mentioned inside the fields' types inside `other_row`.
```ocaml
row_iter other_row (fun (_, ty) -> occurs tv ty);
```
Then we can call our `union_rows` helper and set `other`'s row to be the unioned row.
```ocaml
let row = union_rows env tv_row other_row in
other := Unbound(id, row)
```
Next, if `tv_row` is a `NoRow`, i.e. it's a regular type variable without a row constraint, we do a standard occurs check between `tv` and `ty`.
```ocaml
| _ when equal tv_row NoRow ->
    (* If either type is a type variable, ensure that the type variable does not occur in the type. *)
    occurs tv ty
```
Otherwise, it must mean that `tv_row` has some row constraint and `ty` is not record-shaped, which means unification has failed.
```ocaml
| _ ->
    (* ty is not record-like. Can't unify with a row. *)
    raise (unify_failed t1 t2));
```
If we haven't failed unification by now, we can `Link ty` to `tv`.
Overall, the `TyVar` case of the match looks like
```ocaml
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
        (* If either type is a type variable, ensure that the type variable does not occur in the type. *)
        occurs tv ty
    | _ ->
        (* ty is not record-like. Can't unify with a row. *)
        raise (unify_failed t1 t2));
    (* Link the type variable to the type. *)
    tv := Link ty
```
Finally, `unify` needs to handle the trivial case where two `TyName`s have the same name.
```ocaml
and unify env (t1 : ty) (t2 : ty) : unit =
    ...
    | TyName a, TyName b when equal a b -> () (* The type names are the same. *)
```
With that, we've added type declarations and inference for record literals into our language.

> Aside: Here is the formation rule for user-defined types
> ```
>           TypeBind(T, { l : T_l | l ∈ L }) ∈ Γ    Γ ⊢ T_l type for each l ∈ L 
> WF-Tycon:---------------------------------------------------------------------
>                                        Γ ⊢ T type                             
> ```
> This rule basically says if T is a user-defined type, in order for it to be well-formed, each of its field's types must be well-defined.
> 
> Note: From this point on, Γ needs to be threaded throughout formation rules for well-formedness to hold, including WF-Bool and WF-Arrow. For example, WF-Arrow relies on `A` and `B` being well-formed for `A -> B` to be well-formed.
> 
> The typing rule for records:
> 
> ```
>           TypeBind(T, { l : T_l | l ∈ L }) ∈ Γ    Γ ⊢ e_l : T_l for each l ∈ L 
> T-Record:----------------------------------------------------------------------
>                                Γ ⊢ { l = e_l | l ∈ L } : T                     
> ```
> This says that if there is a type T in the context whose fields match that of the record, the record's type is T.
> 
> The rule for with expressions:
> ```
>         Γ ⊢ r : T    TypeBind(T, { l : T_l | l ∈ L }) ∈ Γ    M ⊆ L    Γ ⊢ e_m : T_m for each m ∈ M 
> T-With:--------------------------------------------------------------------------------------------
>                                     Γ ⊢ { r with m = e_m | m ∈ M } : T                             
> ```
> This says that if r is a record of type T that contains each of the fields in the with expression, then the returned value of the with expression is also of type T.
> 
> and for projection:
> ```
>         Γ ⊢ r : T    TypeBind(T, { l : T_l | l ∈ L }) ∈ Γ    f ∈ L 
> T-Proj:------------------------------------------------------------
>                                Γ ⊢ r.f : T_f                       
> ```
> This says that if r is a record of type T containing a field f, then r.f has the type of that field in T.

Let's take a look at some examples.

You can find and run these examples in [lib/five.ml](lib/five.ml).

### Examples

```ocaml
typecheck_source {|
    type Foo = { x : bool, y : bool -> bool }
    let foo : Foo = { x = true, y = fun x -> x } in foo.y true
|}
```
Output: `bool`

```ocaml
typecheck_source {|
    type Foo = { x : bool }
    let foo : Foo = { x = true } in { foo with y = true }
|}
```
Output: `RowMismatch "{y: bool, ...} and {x: bool}"`

## Polymorphism

Up until now, the language we have type-checked does not have any polymorphism.
For example, in the following program, `f` cannot be applied both to a value of type `A` and to a value of type `B`.
```
type A = {}
type B = {}

let f = fun x -> x in
let a : A = {} in
let b : B = {} in
let _ = f a in
f b
```

Our type inference algorithm gives `f` the type `A -> A`, so when it tries to type-check the application to `B`, it fails.

We'd have to rewrite the example to have a separate `fA` and `fB` to get it to type-check.
```
let fA = fun x -> x in
let fB = fun x -> x in
let a : A = {} in
let b : B = {} in
let _ = fA a in
fB b
```

But when we look at `f`, nothing about its definition requires it to be restricted to `A`. How do we make `f` polymorphic (or generic) over its arguments?

## Instantiation

We'd like `f`'s type to be something like `forall 'a. 'a -> 'a`. But hang on, how would we even use a type like that? We can't exactly unify `'a` with `A`. We need to treat `'a` as a placeholder (or type parameter) that gets substituted with a concrete type argument. This process of taking a generic type and replacing its type parameters with concrete types is called *instantiation*. When `f` gets applied to an `A` or `B`, we look up its type (which will now be generic), and instantiate it to have its type parameters substituted with fresh type variables.

So for example, when `f` is applied to an `A`, `forall 'a. 'a -> 'a` gets instantiated to get `?0 -> ?0`. Then `A -> ?1` gets unified with `?0 -> ?0` as normal, resulting in `A -> A` as the type of the *concrete* instance of `f`.

Likewise, when `f` is applied to a `B`, `forall 'a. 'a -> 'a` gets instantiated to get `?2 -> ?2`, and the same process will result in its concrete type becoming `B -> B`.

To get generic instantiation working, we first want to introduce `generic_ty` that contains a type as well as a list of type parameters.
```ocaml
(* A generic type. Should be read as forall p1..pn. ty, where p1..pn
   are the type parameters. It is separated from ty because in HM, a
   forall can only be at the top level of a type. *)
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
However, this is not very limiting in practice. Most of the polymorphic functions you'd ever want to write can be written in HM.

> Aside: There are some useful exceptions though. For example, Haskell can use the `ST` monad to scope an action to a particular thread with the signature
> ```haskell
> runST :: forall a. (forall s. ST s a) -> a
> ```
> 
> Another example is with existentials, like Rust's `dyn` traits or Go's interface values. These can be encoded with higher-rank polymorphism. `exists X. T` (which is roughly like `dyn Trait`) can be written as `forall Y. (forall X. T -> Y) -> Y`. However, this latter feature can be added on its own, and doesn't necessarily need higher-rank polymorphism/polymorphic lambda calculus/System F.

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

Now let's delve into how `inst` is implemented. Let's run through a simple example first, to get the point across.

Given the generic type `forall 'a 'b. 'a -> ('b -> 'a)`, if `a` had the fresh type variable `?0` and `b` had the fresh type variable `?1`, the instantiated type should be `?0 -> (?1 -> ?0)`.

More concretely, if the `generic_ty` is
```ocaml
{
    type_params = ["'a"; "'b"];
    ty = TyArrow(TyName "'a", TyArrow(TyName "'b", TyName "'a"))
}
```
the instantiated type is something like
```ocaml
let a = TyVar(ref(Unbound("?0", NoRow))) in
let b = TyVar(ref(Unbound("?1", NoRow))) in
TyArrow(a, TyArrow(b, a))
```
(Note: I bound the `TyVar`s to variables here to show that the references would be the same.)

The actual implementation of `inst` just needs to create a hash table mapping from a type parameter to a fresh unbound type variable, traverse over the type, and replace each reference to that type parameter with that type variable. 
```ocaml
  (* Instantiate a generic type by replacing all the type parameters
   with fresh unbound type variables. Ensure that the same ID gets
   mapped to the same unbound type variable by using an (id, ty) Hashtbl. *)
  let inst (gty: generic_ty) : ty =
    let tbl = Hashtbl.create (module String) in
    List.iter gty.type_params ~f:(fun pid ->
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
    if Hashtbl.is_empty tbl then gty.ty else inst' gty.ty
```

The next place things are different is `ELet` (and similarly `ELetRec`). Let's look at how `ELet` changes first. Because a let binding can have annotations and we now have generic types, those annotations can be polymorphic. Perhaps more interestingly, when a let binding is unannotated, it gets inferred to be as polymorphic as possible. This latter behavior is what we mentioned at the beginning of the tutorial as *generalization*. We'll cover the simple case of polymorphic bindings first, which is basically no inference, or rather, how to typecheck a let binding that has a polymorphic type annotation.

What do we want from a polymorphic type annotation? Imagine we had the following program
```
let f : forall 'a. 'a -> 'a = fun x ->
    let y : 'a = x in y
in f true
```
Notice how the annotation on `f` introduces `'a` with a `forall`. `'a` is a type variable that can range over any type, so it can be instantiated with for example, `int`, `bool`, `string`, etc... On the right-hand-side of the let binding, we see a function whose body has another let binding, this time with an annotation mentioning the same `'a`. Basically, if `f` gets instantiated with an `int`, the instantiation's type would be `int -> int`, and the inner let binding's type would be `int`. We can say that the `'a` introduced by `forall 'a` on `f`'s annotation is scoped to the right-hand-side of `f`'s binding.

Another factor we should consider when we have type variables inside annotations is rigidity. What would happen if we tried to instantiate a generic annotation? Let's try to type-check the following program and see what happens:
```
let f : forall 'a 'b. 'a -> 'b = fun x -> x in f
```
To be clear, we do *not* want this to type-check. We assigned an identity function the generic type `forall 'a 'b. 'a -> 'b`, but that implies `'a` and `'b` must be distinct types, whereas in an identity function like `fun x -> x`, the input type must match the output type.

However, when we instantiate this type, we see `TyArrow(?a, ?b)` which `check` tries to `unify` with the function's type `TyArrow(?0, ?0)`, so
```
unify TyArrow(?0, ?0) TyArrow(?a, ?b)
    unify ?0 ?a
        ?0 := Link(?a)
    unify ?0 ?b
        force ?0 = ?a
            unify ?a ?b
                ?a := Link(?b)
```
We just unified `?a` with `?b` and type-checking passed, which is *not* what we want. So how do we fix this?

Well imagine that instead of working with `Unbound` type variables for `?a` and `?b`, we were working with `TyName "a"` and `TyName "b"`. Two `TyName`s with different names are inherently unequal and do not unify. That's the key. We treat type variables as `TyName`s on their own.

```
unify TyArrow(?0, ?0) TyArrow(TyName "a", TyName "b")
  unify ?0 TyName "a"
    ?0 := Link(TyName "a")
  unify ?0 TyName "b"
    force ?0 = TyName "a"
        unify TyName "a" TyName "b"
```
`unify TyName "a" TyName "b"` fails, and so this program doesn't type-check.

What `TyName` is doing here is serving as a *rigid* type variable. That is, unless the type variables have the same name, they do not unify.

Instead of our typical instantiation, we will turn all the type variables in a `generic_ty` into `TyName`s (a.k.a rigid type variables), and extend our environment to hold those names. Extending our environment this way gives us scoping for these type variables, hence these are *scoped* and *rigid* type variables, a lot of jargon to say that the type variables in an annotation get put in our environment and get referenced as type names.

To implement this, first, we will introduce another kind of binding to our environment called `TypeVarBind`. This just indicates that a name we look up is in fact a type variable.
```ocaml
type bind =
    ...
    | TypeVarBind (* A type variable binding marks some rigid type. *)
```
Then, we'll update our environment to hold `TypeVarBind`s for every type parameter in our generic type. This is where we make our annotation rigid. We don't need to modify the body of the type, because if we aren't calling `inst`, references to the type variable are just `TyName`s.
```ocaml
(* Turn a generic_ty into its rigid form, so that when annotations are instantiated, 
   they don't produce Unbound type variables that can unify with each other.*)
let as_rigid (gty: generic_ty) : env * ty =
    let extras = List.map gty.type_params ~f:(fun id -> (id, TypeVarBind)) in
    (extras, gty.ty)
```

For the `unify` trace from earlier to actually reject the invalid program, we need to update `unify` to handle `TypeVarBind`. We generalize `lookup_tycon` into a `lookup_binding` function that returns any binding, and the `TyName` arm becomes

```ocaml
| TyName tname ->
  (match lookup_binding tname env with
   | TypeVarBind ->
     (match tv_row with
      | NoRow -> ()
      | _ -> raise (expected_ty_error "record" tname))
   | TypeBind tc -> ignore (union_rows env tv_row (ClosedRow tc.ty))
   | VarBind _ -> raise (undefined_error "type" tname))
```

Now let's look at how we modify `ELet`.
```ocaml
match ann with
| Some ann ->
    let (extras, check_ty) = as_rigid ann in
    check (extras @ env) check_ty rhs
| None -> infer env rhs
```
In the case where there is a generic annotation, we extend the environment with its type parameters (`extras`), and type-check the right-hand-side. The annotation puts us back in checking mode, and the rigid type variables introduced by `as_rigid` mean the check enforces the polymorphic annotation rather than falling back to inference.

Now what if we want to have a generic function that doesn't need a type annotation? This is where generalization comes in.

## Generalization

Now that we've covered instantiation of generic types and checking generic annotations, it's time to get to the meat of Hindley-Milner--generalization. Simply put, generalization takes a type that's not generic and makes it generic by turning its unbound type variables into type parameters.

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

The rule is that a type variable on the right-hand-side of a let binding is only generalized if it was created in the right-hand-side of that let binding. So in other words, for an expression like
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
  | Unbound of id * row_constraint * scope
    (* Unbound type variable: Holds the type variable's unique name, any
       row constraint, and the scope at which it was created. *)
  | Link of ty (* Link type variable: Holds a reference to a type. *)

(* Generate a fresh unbound type variable with a unique name, an optional
   row constraint, and the current scope. *)
let fresh_unbound_var ?(row=NoRow) () =
    let n = !gensym_counter in
    Int.incr gensym_counter;
    let tvar = "?" ^ Int.to_string n in
    TyVar (ref (Unbound (tvar, row, !current_scope)))
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
| TyVar ({ contents = Unbound (id, tgt_row, tgt_scope) } as tgt) ->
    (* Recurse into the target's row constraint to lower scopes there too. *)
    row_iter tgt_row (fun (_, ty) -> occurs src ty);
    (* Grab src and tgt's scopes. *)
    let { contents = Unbound(_, _, src_scope) } = src in
    (* Compute the minimum of their scopes (the outermost scope). *)
    let min_scope = min src_scope tgt_scope in
    (* Update the tgt's scope to be the minimum, preserving its row. *)
    tgt := Unbound (id, tgt_row, min_scope)
```

Since `Unbound` carries `row_constraint` as well as `scope` now, the destructure and update both have to include it. We also recurse into the row's types so their scopes get lowered too.

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
    | TyVar ({ contents = Unbound (id, tgt_row, tgt_scope) } as tgt) ->
        row_iter tgt_row (fun (_, ty) -> occurs src ty);
        let { contents = Unbound(_, _, src_scope) } = src in
        let min_scope = min src_scope tgt_scope in
        tgt := Unbound (id, tgt_row, min_scope)
    | TyArrow(from, dst) ->
        occurs src from;
        occurs src dst;
    | _ -> ()
```

To fully ensure that the scope of a type variable gets updated to be the outermost one, we also need to update the TyVar-TyVar arm in `unify` that unions row constraints. That arm doesn't go through the `occurs` check, so we set the min scope there directly:
```ocaml
| TyVar other when not (phys_equal tv other) ->
    let Unbound(id, other_row, other_scope) = !other in
    row_iter other_row (fun (_, ty) -> occurs tv ty);
    let min_scope = min src_scope other_scope in
    let row = union_rows env tv_row other_row in
    other := Unbound(id, row, min_scope)
```
The change is just pulling out `other_scope`, taking the minimum with `src_scope`, and stamping it on the updated `other`.

Now let's actually look into how generalization is implemented. `gen` will be a function that accepts a `ty` and returns a `generic_ty`.
```ocaml
let gen (ty: ty) : generic_ty =
    let type_params = Hash_set.create (module String) in
```
We want to walk over the type to find all of its type variables, and grab the `id`s of the ones whose scope is greater than the `current_scope`. We keep track of those ids in a `Hash_set` called `type_params`. Those will be the type parameters in our generalized type.

We create a helper (`gen'`) to recur down the type and return the generalized type. The first case is the only interesting one (the rest are just recurring over the `ty`). If the `scope` of the `Unbound` type variable is greater than `current_scope`, we add the type variable's `id` to the `type_params` hash set and return up a `TyName` with that `id` to reference that type parameter. (Remember when `inst`antiation comes around, it will look for `TyName`s that correspond to those type parameters.) We also mutate the tvar to `Link` to the generalized `TyName`, so any later code that walks the typed AST doesn't see it as still Unbound.
```ocaml
let rec gen' ty =
    match force ty with
    | TyVar ({ contents = Unbound (id, _, scope) } as tv) when scope > !current_scope ->
        Hash_set.add type_params id;
        tv := Link (TyName id);
        TyName id
    | TyArrow (from, dst) -> TyArrow (gen' from, gen' dst)
    | ty -> ty
in
```
We ignore the row constraint for now and come back to it when we handle row polymorphism.
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
        | TyVar ({ contents = Unbound (id, _, scope) } as tv) when scope > !current_scope ->
            Hash_set.add type_params id;
            tv := Link (TyName id);
            TyName id
        | TyArrow (from, dst) -> TyArrow (gen' from, gen' dst)
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
        | Some ann ->
            let (extras, check_ty) = as_rigid ann in
            check (extras @ env) check_ty rhs
        | None -> infer env rhs
    in
    leave_scope();
    ...
```
On top of this change, we want to generalize the type of the right-hand-side when there's no annotation. If there is an annotation, we already have the polymorphic type we want, so we use the annotation directly.
```ocaml
let ty_gen =
    match ann with
    | Some ann -> ann
    | None -> gen (typ rhs)
in
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
    let env = (id, VarBind ty_gen) :: env in
    let body = infer env body in
    TELet ((id, ann, rhs), body, typ body)
```

### Try let generalization

Here's a tool to visualize the process of let generalization. Pick the naive rule or the scope-checked one, then step through to see how the trace differs between them.

<!-- widget: let-generalization-scope -->

The `ELetRec` case is slightly more complicated. To type-check recursive let bindings, we want to *delay* generalization until after each let binding is inferred. This means that mutually recursive bindings will not be referencing generic versions of each other. Why is this? Turns out that referencing generic versions of each other while fully inferring their types is undecidable.

Here is an example of polymorphic recursion from the [ocaml docs](https://v2.ocaml.org/manual/polymorphism.html#s%3Apolymorphic-recursion).
```ocaml
type 'a nested =
    | List of 'a list
    | Nested of 'a list nested

let rec depth = function
    | List _ -> 1
    | Nested n -> 1 + depth n
```

Looks like a fairly simple function, but the issue here is that the inner call to `depth n` ends up trying to unify `'a nested` with `'a list nested`, which is not satisfiable. The type-checker doesn't realize that the `'a nested` `depth` was initially called on is different from the `'a list nested` that's the element type. This can be solved by providing an explicit annotation to `depth`, like `forall 'a. 'a nested -> int`. However, there are other issues related to polymorphic recursion in that it can't be monomorphized, and leads to inefficient implementation. In practice, not having polymorphic recursion is not an issue. Most of the recursive functions you'll ever want to define can be written and inferred in this setting.

> Aside: The undecidability of type inference for polymorphic recursion was shown by Fritz Henglein in the paper "Type Inference with Polymorphic Recursion". They show that semi-unification reduces to type inference for polymorphic recursion, which implies it's undecidable.

We still want to `enter_scope()` at the beginning. After that, we run `as_rigid` on each declaration's annotation (if it has one), storing the result in a list called `prepared` so we can reuse it across the next few passes.
```ocaml
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
```
When we map over each prepared declaration to add its binding to the environment, since we aren't generalizing until later, we just want to add the non-generalized versions by wrapping each `check_ty` in `dont_generalize`. This time, the extended environment is set to a variable named `env_with_decls` instead of `env`, because we want to keep the old `env` around so we can add the generalized bindings.
```ocaml
let env_decls = List.map prepared ~f:(fun (id, _, _, _, check_ty) ->
    (id, VarBind (dont_generalize check_ty)))
in
let env_with_decls = env_decls @ env in
```
When we check the right-hand-side of the declarations using the types in the extended environment (`env_with_decls`), we add the rigid `extras` to it and check against `check_ty`. After all of the right-hand-side expressions in the recursive let binding have been inferred, then we can `leave_scope()`. This list of declarations needs to be a `tlet_decl list`, since that's what `TELetRec` expects.
```ocaml
let tdecls : tlet_decl list = List.map prepared ~f:(fun (id, ann, rhs, extras, check_ty) ->
    let trhs = check (extras @ env_with_decls) check_ty rhs in
    (id, ann, trhs))
in
leave_scope();
```
Now we generalize the types of all the bindings. As with `ELet`, if there's an annotation we use it directly, otherwise we call `gen` on the inferred type.
```ocaml
let generalized_bindings = List.map tdecls ~f:(fun (id, ann, rhs) ->
    let ty_gen =
        match ann with
        | Some ann -> ann
        | None -> gen (typ rhs)
    in
    (id, VarBind ty_gen))
in
```
Finally, we add it to the original `env` so we can use it to infer the body of the recursive let binding.
```ocaml
let env_body = generalized_bindings @ env in
let body = infer env_body body in
TELetRec (tdecls, body, typ body)
```

Overall, our updated implementation of `ELetRec` looks like
```ocaml
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
```

> Aside: Here's our typing rule for `ELet`.
> 
> ```
>        Γ ⊢ rhs : A    vars = FV(A) \ FV(Γ)    Γ, VarBind(x, ∀ vars. A) ⊢ body : B 
> T-Let:----------------------------------------------------------------------------
>                                Γ ⊢ let x = rhs in body : B                        
> ```
> 
> `FV(A)` and `FV(Γ)` are the sets of type variables that appear free in `A` and `Γ` respectively. We write `vars` for `FV(A) \ FV(Γ)`, the type variables free in `A` but not in `Γ`. This rule basically says that if `rhs` has the type `A` in `Γ`, and `Γ` extended with `x` having the type `∀ vars. A` lets us give the body the type `B`, then `let x = rhs in body` has type `B`.
> 
> And here's our typing rule for `ELetRec`.
> 
> ```
>           Γ_rec = Γ, { VarBind(x, A_x) | x ∈ decls }          vars_x = FV(A_x) \ FV(Γ) for each x ∈ decls 
>          ---------------------------------------------------------------------------------------------------
> T-LetRec: Γ_rec ⊢ rhs_x : A_x for each x ∈ decls    Γ, { VarBind(x, ∀ vars_x. A_x) | x ∈ decls } ⊢ body : B 
>          ---------------------------------------------------------------------------------------------------
>                                   Γ ⊢ let rec { x = rhs_x | x ∈ decls } in body : B                        
> ```
> 
> Here, we have the same `decls`, `A_x`, `rhs_x`, and `Γ_rec` as in the original T-LetRec rule. `vars_x` is the set of type variables we generalize for the binding `x`. This rule basically says that if each `rhs_x` has the type `A_x` in `Γ_rec`, and `Γ` extended with each `x` having the type `∀ vars_x. A_x` lets us give the body the type `B`, then `let rec { x = rhs_x | x ∈ decls } in body` has type `B`. Note that when the rhs is inferred, `x` is not polymorphic (i.e. it's a monotype), so in our formulation of T-LetRec, polymorphic recursion isn't supported.
> 
> The original Damas-Milner formulation factors generalization out as its own rule:
> 
> ```
>           Γ ⊢ e : A    a ∉ FV(Γ) 
> T-Gen-DM:------------------------
>                Γ ⊢ e : ∀a. A     
> ```
> 
> This says that if `e` has the type `A` in `Γ`, and `a` is any type variable not free in `Γ`, then `e` can be given the type `∀a. A`. With T-Gen-DM in place, the simpler versions of T-Let and T-LetRec don't need to generalize themselves. They assume `A` is already polymorphic where needed, and just thread it through. Chaining applications of T-Gen-DM for each variable in `FV(A) \ FV(Γ)` gives us the same generalization present in our T-Let and T-LetRec rules.

Woo! That was a doozy. But we got through it now. How about we take a look at some examples to celebrate?

You can find and run these examples in [lib/six.ml](lib/six.ml).

### Examples

```ocaml
typecheck_source {|
    type A = {}
    let a : A = {} in
    let f = fun x -> x in
    let _ = f a in
    f true
|}
```
Output: `bool`

```ocaml
typecheck_source {|
    let rec fix = fun f -> fun x -> f (fix f) x in
    fix (fun f -> fun arg -> if arg then f false else true)
|}
```
Output: `bool -> bool`

```ocaml
typecheck_source {|
    type A = {}
    let a : A = {} in
    let f : forall 'a. 'a -> bool = fun x -> true in
    f a
|}
```
Output: `bool`

```ocaml
typecheck_source {|
    type A = {}
    let f : forall 'a. 'a -> A = fun x -> true in
    f true
|}
```
Output: `TypeError "expression does not have type 'a -> A"`

```ocaml
typecheck_source "(fun x -> let y = x in y) true true"
```
Output: `UnificationFailure "failed to unify type bool with bool -> ?2"`

## Row polymorphism

Currently, we are able to infer the types of expressions involving records, as long as they ultimately unify to some concrete type. However, one of the beautiful things about let generalization in Hindley-Milner is that we can define a function without a type signature that can operate on values of different types. What if we could apply that polymorphism to records?

For example, given the records
```
type Foo = { x : bool }
type Bar = { x : bool -> bool }
let r1 : Foo = { x = true } in
let r2 : Bar = { x = fun y -> y } in
```
and the function
```
let f = fun r -> r.x in
```
We'd like to be able to invoke `f` on both records, that is `f r1` and `f r2`. There's no reason why `r.x` can't operate on both records, since they both have fields named `x`. Similarly with `{ r with x = true }`, the only requirement on `r` is that it contain a field `x` whose type is `bool`. How do we encode this in our type system?

Recall when inferring the type of record projection, we give the record a fresh unbound type variable with an `OpenRow` constraint. We expressed to the type-checker "we don't know what record this is but we know it should contain a field named `x`." So at the expression level, that constraint is already attached to the `Unbound` type variable for `r`.

The problem is what happens at generalization. When `f` is normally generalized, the `OpenRow` constraint isn't preserved, so you end up with `forall 'a 'b. 'a -> 'b`. We need some way of encoding that `'a` is a record with a field `x : 'b`.

Here's the syntax for that:
```
forall 'a 'b. 'a :: { x : 'b, ... } => 'a -> 'b
```
The piece between `::` and `=>` is a row constraint, and it corresponds directly to the `OpenRow` the expression-level inference produced for `r`. So row polymorphism is really about carrying that constraint through `gen`, `inst`, and `unify`. The expression-level inference doesn't have to change at all.

> Aside: Our approach borrows ideas from Atsushi Ohori's [A Polymorphic Record Calculus and Its Compilation](https://dl.acm.org/doi/10.1145/218570.218572), including the `::` syntax for kind-based constraints on type variables. There are many other approaches to row polymorphism. Mitchell Wand's original row variables and Didier Rémy's presence/absence type system handle simple rows where labels must be unique. Daan Leijen's [Extensible records with scoped labels](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/scopedlabels.pdf) lifts that restriction with scoped rows. More recent work by Morris and McKinna in [Abstracting Extensible Data Types: Or, Rows by Any Other Name](https://dl.acm.org/doi/10.1145/3290325) introduces a system called Rose that abstracts over rows via qualified types and captures both simple and scoped rows. Its successor, [Generic Programming with Extensible Data Types](https://dl.acm.org/doi/10.1145/3607843) by Hubers and Morris, extends Rose with first-class labels and generic programming over rows, enabling polymorphic equality on extensible records and variants.

Okay so given that type signature, it's clear we need to update `generic_ty` and `TypeVarBind` to carry row constraints. Then we need to update `gen`, `inst`, and `unify` accordingly.
```ocaml
type generic_ty = {
    type_params : (id * row_constraint) list;
    ty : ty;
}
```
Similarly, we want type variables sitting in our environment to hold onto those row constraints as well.
```ocaml
type bind =
    ...
    | TypeVarBind of row_constraint
```
And correspondingly, we have to update the producers and consumers of `generic_ty`. Let's start with the simplest: `as_rigid`.
```ocaml
let as_rigid (gty: generic_ty) : env * ty =
    let extras = List.map gty.type_params ~f:(fun (id, row) -> (id, TypeVarBind row)) in
    (extras, gty.ty)
```
Next, let's update `gen`. We're going to create a small helper to map over the fields of a row constraint.
```ocaml
let map_row ~f row =
    match row with
    | NoRow -> NoRow
    | OpenRow flds -> OpenRow (List.map flds ~f:(fun (id, ty) -> (id, f ty)))
    | ClosedRow flds -> ClosedRow (List.map flds ~f:(fun (id, ty) -> (id, f ty)))
```
Now `gen` just needs to map over the row constraint to generalize unbound type variables present in the row constraint.
```ocaml
| TyVar ({ contents = Unbound (id, row, scope) } as tv) when scope > !current_scope ->
    Hashtbl.set type_params ~key:id ~data:(map_row ~f:gen' row);
```
We also change `type_params` from a `Hash_set` to a `Hashtbl` so we can map a type variable to its row_constraint.

Overall, our `gen` implementation looks like
```ocaml
let gen (ty: ty) : generic_ty =
    let type_params : (id, row_constraint) Hashtbl.t = Hashtbl.create (module String) in
    let rec gen' ty =
        match force ty with
        | TyVar ({ contents = Unbound (id, row, scope) } as tv) when scope > !current_scope ->
            Hashtbl.set type_params ~key:id ~data:(map_row ~f:gen' row);
            tv := Link (TyName id);
            TyName id
        | TyArrow (from, dst) -> TyArrow (gen' from, gen' dst)
        | ty -> ty
    in
    let ty = gen' ty in
    let type_params =
        Hashtbl.to_alist type_params
        |> List.sort ~compare:(fun (a,_) (b,_) -> String.compare a b)
    in
    { type_params; ty }
```

Similarly, we update `inst`. It's mostly the same as before: create fresh type variables for each type parameter, then walk the type body replacing each `TyName` with its corresponding type variable.

However, this time, we need to also preserve whatever row constraint the type parameter had, recursing over the row to instantiate its type variables as well.

Overall, our `inst` implementation looks like
```ocaml
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
    (* Attach the instantiated row constraint to each fresh type variable in the table. *)
    List.iter gty.type_params ~f:(fun (pid, row) ->
        match row with
        | NoRow -> ()
        | _ ->
            match Hashtbl.find_exn tbl pid with
            | TyVar tv ->
                let Unbound(id, _, scope) = !tv in
                tv := Unbound(id, map_row ~f:inst' row, scope)
            | _ -> failwith "unreachable: tbl always holds TyVars");
    inst' gty.ty
```
We now need to update `unify` to handle type variables that carry row constraints, like those in a type annotation that `as_rigid` puts in env as rigid TyNames. We need to ensure that fields in a type variable's row constraint exist in the rigid type's row constraint. We'll pull this into a helper called `check_rigid_subset`.
If the type variable has no row constraint, it's trivially a subset of anything else.
```ocaml
and check_rigid_subset env tname tv_row rigid_row =
    match tv_row, rigid_row with
    | NoRow, _ -> ()
    ...
```
If the type variable has a row but the rigid type doesn't, then the rigid type isn't record-shaped, so we throw an error.
```ocaml
| _, NoRow -> raise (expected_ty_error "record" tname)
...
```
If the type variable has an OpenRow, we check if each of its fields exists in the rigid type's row by calling `fld_exists`, which if you recall tries to unify the field's type.
```ocaml
| OpenRow flds, OpenRow rigid_flds
| OpenRow flds, ClosedRow rigid_flds ->
    List.iter flds ~f:(fun (id, ty) ->
    if not (fld_exists env rigid_flds id ty) then
        raise (row_mismatch tv_row rigid_row))
...
```
The catch-all covers when the type variable has a ClosedRow, which means it's a record literal that hasn't found its nominal type yet. A rigid type variable isn't a nominal type so they can't be bound.
```ocaml
| _ -> raise (row_mismatch tv_row rigid_row)
```
Overall, `check_rigid_subset` looks like
```ocaml
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
```
Now the `TypeVarBind` case just becomes a call to `check_rigid_subset`.
```ocaml
| TyVar tv, ty | ty, TyVar tv ->
    let Unbound(_, tv_row, _) = !tv in
    (match ty with
    | TyName tname ->
        (match lookup_binding tname env with
        | TypeVarBind rigid_row -> check_rigid_subset env tname tv_row rigid_row
        ...)
    ...
```

> Aside: Here are the typing rules for projection and with-expressions on row-polymorphic type variables. They mirror T-Proj and T-With from the section on [Type declarations](#type-declarations), but get their fields from `TypeVarBind` instead of `TypeBind`.
> 
> ```
>             Γ ⊢ r : a    TypeVarBind(a, { l : T_l | l ∈ L, ... }) ∈ Γ    f ∈ L 
> T-Proj-Row:--------------------------------------------------------------------
>                                        Γ ⊢ r.f : T_f                           
> ```
> 
> ```
>             Γ ⊢ r : a    TypeVarBind(a, { l : T_l | l ∈ L, ... }) ∈ Γ    M ⊆ L    Γ ⊢ e_m : T_m for each m ∈ M 
> T-With-Row:----------------------------------------------------------------------------------------------------
>                                             Γ ⊢ { r with m = e_m | m ∈ M } : a                                 
> ```
> 
> We update the T-Let rule to hold row constraints in the quantified type, where the row constraint for type variable `a` is denoted by `R_a`.
> 
> ```
>                                 Γ ⊢ rhs : A                          
>       ---------------------------------------------------------------
>        vars = FV(A) \ FV(Γ)    constraints = { a :: R_a | a ∈ vars } 
> T-Let:---------------------------------------------------------------
>              Γ, VarBind(x, ∀ vars. constraints => A) ⊢ body : B      
>       ---------------------------------------------------------------
>                         Γ ⊢ let x = rhs in body : B                  
> ```
> 
> T-LetRec is similarly updated to carry row constraints in polymorphic types, but for each binding.
> 
> ```
>                                               Γ_rec = Γ, { VarBind(x, A_x) | x ∈ decls }                                     
>          --------------------------------------------------------------------------------------------------------------------
>           vars_x = FV(A_x) \ FV(Γ) for each x ∈ decls           constraints_x = { a :: R_a | a ∈ vars_x } for each x ∈ decls 
> T-LetRec:--------------------------------------------------------------------------------------------------------------------
>           Γ_rec ⊢ rhs_x : A_x for each x ∈ decls    Γ, { VarBind(x, ∀ vars_x. constraints_x => A_x) | x ∈ decls } ⊢ body : B 
>          --------------------------------------------------------------------------------------------------------------------
>                                            Γ ⊢ let rec { x = rhs_x | x ∈ decls } in body : B                                 
> ```

Now let's look at some examples.

You can find and run these examples in [lib/seven.ml](lib/seven.ml).

### Examples

In this example, `'r` is a rigid type variable in the environment with an OpenRow constraint `{ x : bool, ... }`. The body's `r.x` creates an OpenRow constraint `{ x : ?_ }` on `r`'s type variable. `check_rigid_subset` confirms `r`'s row is contained in `'r`'s row.
```ocaml
typecheck_source {|
    type Foo = { x : bool, y : bool }
    let get_x : forall 'r. 'r :: { x : bool, ... } => 'r -> bool =
        fun r -> r.x
    in
    let foo : Foo = { x = true, y = false } in
    get_x foo
|}
```
Output: `bool`

In this example, `gen` gives `f` a row-polymorphic type, a function whose input can be any record with an `x` field. Each application instantiates `f`'s type to a fresh type variable with an OpenRow constraint, which is unified with the argument.
```ocaml
typecheck_source {|
    type Foo = { x : bool }
    type Bar = { x : bool -> bool }
    let r1 : Foo = { x = true } in
    let r2 : Bar = { x = fun y -> y } in
    let f = fun r -> r.x in
    let _ = f r1 in
    f r2
|}
```
Output: `bool -> bool`

In this example, `get_x`'s type is instantiated to a fresh type variable with the OpenRow constraint `{ x : bool, ... }`. That type variable is unified with `Foo`, but when unify tries to union their fields together, it finds that `Foo` doesn't have an `x` field.
```ocaml
typecheck_source {|
    type Foo = { y : bool }
    let get_x : forall 'r. 'r :: { x : bool, ... } => 'r -> bool =
    fun r -> r.x
    in
    let foo : Foo = { y = true } in
    get_x foo
|}
```
Output: `RowMismatch "{x: bool, ...} and {y: bool}"`

That's row polymorphism! We can write functions that are polymorphic over the record types they operate on. Note that we didn't have to touch `infer` at all. All of our changes happened with `generic_ty`, `gen`, `inst`, `unify`, plus some new helpers. This makes sense given that nothing about our expression language has changed. We just want to make our functions more generic.

## Generic type declarations

You'll notice in our examples above, the type declarations are not generic. However, in languages like Java or ML, you have access to types like `List` that are instantiated with some type argument. Similarly to row polymorphism, we won't need to change anything about our expression-level inference. All of the work happens at the level of `gen`, `inst`, `unify`, and `occurs`. The first thing we'll want to do is modify our definition of `tycon` to contain type parameters.
```ocaml
type tycon = {
    name : id;
    type_params : id list;
    ty : record_ty;
}
```
This allows us to write definitions like
```
type Box<T> = {
    x: T
}
```
where `Box` is a type constructor with a single type parameter. We need some way to represent a concrete type like `Box<bool>`, which is the result of type *application*. We will modify our `ty` definition to add a `TyApp` variant.
```ocaml
type ty =
    ...
    | TyApp of ty list (* Type application: head :: args, e.g. TyApp[TyName "box"; TyBool] *)
```
A `Box<Bool>` would be represented as `TyApp [TyName "Box"; TyBool]`.

Next, we need to update our `gen`, `inst`, and `occurs` implementations to handle `TyApp`. They all follow the same pattern of recursively mapping over the `TyApp`'s list.

Here's `gen`:
```ocaml
let rec gen' ty =
    match force ty with
    ...
    | TyApp app -> TyApp (List.map app ~f:gen')
    ...
```
Here's `inst`:
```ocaml
let rec inst' ty =
    match force ty with
    ...
    | TyApp app -> TyApp (List.map app ~f:inst')
    ...
```
And here's `occurs`:
```ocaml
let rec occurs (src : tv ref) (ty : ty) : unit =
    match force ty with
    ...
    | TyApp app -> List.iter app ~f:(occurs src)
    ...
```
We now want to update `unify` to handle type applications. Conceptually, this is divided into two cases. The first is the case where you have two `TyApp`s and want to unify them. This is just a matter of checking that their type argument lists unify. That is, they are the same length and that each type argument of the first list unifies with the corresponding type argument of the second list.
```ocaml
and unify env (t1 : ty) (t2 : ty) : unit =
    ...
    | TyApp app1, TyApp app2 when List.length app1 = List.length app2 ->
      List.iter2_exn app1 app2 ~f:(unify env)
    ...
```
The second case is where a type variable gets unified with a reference to some pre-declared type constructor that is possibly applied to some arguments. This case takes effect in `unify` where one of the two types is a `TyVar`.
```ocaml
match (t1, t2) with
...
| TyVar tv, ty | ty, TyVar tv ->
  ...
```
This case is split so we can handle when the other `ty` is either `TyName` (just a type constructor's name) or `TyApp` (a type constructor applied to type arguments). For example, this would be the first case, where we'd unify `Foo` with `ClosedRow { x: bool }`.
```
type Foo = { x: bool }
let foo : Foo = { x = true } in foo
```
For `Foo`, there's nothing to apply. Its fields `{ x: bool }` are already what we want to unify against.

And this would be the second case, where we'd unify `Box bool` with `ClosedRow { x: bool }`.
```
type Box 'a = { x: 'a }
let box : Box bool = { x = true } in box
```
However, here we want to actually apply the type. That is, we want to substitute `bool` into the argument for `Box` to get a `{ x: bool }` we can actually unify against.

We define a helper `apply_tyapp` to do this for us.
```ocaml
let apply_tyapp env (ty : ty) : record_ty =
    match force ty with
    ...
```
If it's a `TyName`, there's nothing to apply. We just look the binding up in the environment, expecting a `TypeBind` holding a type constructor. Before we return its underlying record fields, we validate that the type constructor's argument list is empty, since we don't want someone to be referring to a type like `Box` in an annotation without fully applying it.
```ocaml
| TyName name ->
  (match lookup_binding name env with
  | TypeBind tc when List.is_empty tc.type_params -> tc.ty
  | TypeBind _ -> raise (cannot_apply name)
  | TypeVarBind _ | VarBind _ -> raise (undefined_error "type" name))
```
If it's a `TyApp`, we still look up the binding, but now we have to substitute all the type arguments (like `bool` in `Box bool`) for the type parameters (like `'a` in `Box 'a`) wherever they show up in the underlying record type (so `{ x : bool }` instead of `{ x : 'a }`). If you recall back in the [Instantiation](#instantiation) section, we also perform substitution on types. Turns out, if we create a hash table mapping from the type parameters to their corresponding type arguments, we can use the same exact logic for substitution here. Let's first avoid some duplication by extracting out the substitution logic in a helper (`inst` now calls `substitute` instead of `inst'`).
```ocaml
let rec substitute (tbl : (id, ty) Hashtbl.t) (ty : ty) : ty =
    match force ty with
    | TyName id as ty ->
        (match Hashtbl.find tbl id with
        | Some t -> t
        | None -> ty)
    | TyArrow (from, dst) -> TyArrow (substitute tbl from, substitute tbl dst)
    | TyApp app -> TyApp (List.map app ~f:(substitute tbl))
    | ty -> ty
```
And our type application logic just maps over the record fields of a type constructor, and substitutes each field's type using our table, returning the resultant record.
```ocaml
| TyApp (TyName name :: args) ->
  (match lookup_binding name env with
  | TypeBind tc ->
    (match List.zip tc.type_params args with
     | Ok pairs ->
       let tbl = Hashtbl.of_alist_exn (module String) pairs in
       List.map tc.ty ~f:(fun (id, t) -> (id, substitute tbl t))
     | Unequal_lengths -> raise (cannot_apply name))
  | TypeVarBind _ | VarBind _ -> raise (undefined_error "type" name))
```
Finally, if we don't see a `TyName` or `TyApp`, we throw an error.
```ocaml
| _ -> failwith "apply_tyapp: expected TyName or TyApp"
```
Overall, our `apply_tyapp` function looks like
```ocaml
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
```
That might've seemed like a long detour but let's reorient ourselves. We're back to updating `unify` under the `TyVar` branch. We want to handle the cases where the other type is a `TyName` or `TyApp` corresponding to some type constructor.

Here's how we handle these cases:
```ocaml
match (t1, t2) with
...
| TyVar tv, ty | ty, TyVar tv ->
  let Unbound(_, tv_row, src_scope) = !tv in
  (match ty with
   | TyName tname ->
     (match lookup_binding tname env with
      ...
      | TypeBind _ ->
        let tycon_row = ClosedRow (apply_tyapp env ty) in
        ignore (union_rows env tv_row tycon_row))
   | TyApp _ ->
     let tycon_row = ClosedRow (apply_tyapp env ty) in
     ignore (union_rows env tv_row tycon_row)
```
We apply the type to get its underlying record type and union its row constraints with those of our type variable that we're unifying.

> Aside: We update our formation rules for type constructors by updating `TypeBind` to carry a list of type parameters.
> 
> ```
>           TypeBind(T, params, _) ∈ Γ    Γ ⊢ arg_p type for each p ∈ params 
> WF-Tycon:------------------------------------------------------------------
>                                    Γ ⊢ T args type                         
> ```
> 
> We add T-Record-App, T-Proj-App, and T-With-App to mirror T-Record, T-Proj, and T-With from the section on [Type declarations](#type-declarations), but they substitute the type arguments into the tycon's body. We write `T[params ↦ args]` for `T` with each parameter in `params` replaced by the corresponding argument in `args`.
> 
> ```
>               TypeBind(T, params, { l : T_l | l ∈ L }) ∈ Γ    Γ ⊢ arg_p type for each p ∈ params    Γ ⊢ e_l : T_l[params ↦ args] for each l ∈ L 
> T-Record-App:-----------------------------------------------------------------------------------------------------------------------------------
>                                                                Γ ⊢ { l = e_l | l ∈ L } : T args                                                 
> ```
> 
> ```
>             Γ ⊢ r : T args    TypeBind(T, params, { l : T_l | l ∈ L }) ∈ Γ    f ∈ L 
> T-Proj-App:-------------------------------------------------------------------------
>                                   Γ ⊢ r.f : T_f[params ↦ args]                      
> ```
> 
> ```
>             Γ ⊢ r : T args    TypeBind(T, params, { l : T_l | l ∈ L }) ∈ Γ    M ⊆ L    Γ ⊢ e_m : T_m[params ↦ args] for each m ∈ M 
> T-With-App:------------------------------------------------------------------------------------------------------------------------
>                                                     Γ ⊢ { r with m = e_m | m ∈ M } : T args                                        
> ```

And so ends our process of typechecking generic type declarations! Let's look at some examples.

You can find and run these examples in [lib/eight.ml](lib/eight.ml).

### Examples

Here's the `box bool` example from earlier. `{ x = true }` is inferred as a `ClosedRow { x : bool }` that's checked against the annotation. `apply_tyapp` takes `box` and substitutes `bool` for `'a` in its body, giving us `{ x : bool }`, which matches that closed row constraint.
```ocaml
typecheck_source {|
    type box 'a = { x : 'a }
    let r : box bool = { x = true } in r.x
|}
```
Output: `bool`

Here's an identity function of the type `forall 'a. box 'a -> box 'a`. It gets instantiated to `box ?0 -> box ?0`, so when it's applied to `r`, `box ?0` gets unified with `box bool`. This will hit the `(TyApp, TyApp)` case of our `unify`.
```ocaml
typecheck_source {|
    type box 'a = { x : 'a }
    let identity : forall 'a. box 'a -> box 'a = fun b -> b in
    identity (let r : box bool = { x = true } in r)
|}
```
Output: `box bool`

Here's a case where the literal's fields don't match the type constructor's. `box` requires `x` and `y`, but the literal only provides `x`. Going through the same route as before in `apply_tyapp`, we find that `{ x : bool, y : bool }` doesn't unify with `ClosedRow { x : bool }`, so we raise a `RowMismatch`.
```ocaml
typecheck_source {|
    type box 'a = { x : 'a, y : bool }
    let r : box bool = { x = true } in r.x
|}
```
Output: `RowMismatch "{x: bool} and {x: bool, y: bool}"`

## Side effects

Up until now, this language has been pure. You would think adding features like mutability and other side effects would not be a problem for a polymorphic type system like ours. However, there are gotchas. Let's say we added mutability to our language with a `Ref 'a` type. For example, `Ref int` corresponds to a memory location containing an `int` value. A `Ref 'a` can be built with a `ref` function, whose type is `forall 'a. 'a -> Ref 'a`. You can retrieve the value at a `Ref 'a` via `deref`, whose type is `forall 'a. Ref 'a -> 'a`. A shorthand operator for this is `*r`, where `r` is the name of the reference. Finally, you can update the value at an existing memory location via `update`, whose type is `forall 'a. Ref 'a -> 'a -> Unit` (`Unit` is just an empty record type). A shorthand syntax for this operation is `*r = v`, where `r` is the name of the reference and `v` is the value being stored.

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
let a : A = {} in
(*r) a
```
In this example, we create a reference to a lambda and then generalize it. `r` would have the generic type `forall 'a. Ref('a -> bool)`. The third line instantiates the generic type to be `Ref(?0 -> bool)` and unifies `?0 -> bool` with the right-hand-side, whose type is `bool -> bool`. All well and good.

Now comes a problem. The last line again instantiates the generic type to get `Ref(?1 -> bool)`, dereferences it, and applies the lambda to `a`. The type-checker accepts this program.

However, if we actually run this, the third line stores a lambda that accepts a `bool`ean condition and does `if condition then ...` to it. And the fifth line invokes that lambda on a value of type `A`. But `A` is not a `bool`!

What we learn from this example is that by generalizing a variable that is mutable, each instantiation gets to ignore changes to the type that other updates made to that memory location. We don't want that, because it means our program is not type-safe! In other words, the evaluator of this language would reach an invalid state at runtime when it tries to do `if a then ...`, since `A` is not `bool`.

What can we do about this? The immediate answer is to not generalize expressions like `ref <exp>`, so we just end up with `r`'s type as `Ref(?0 -> bool)`. Then when the third line updates the location to hold `bool -> bool`, that information gets carried into the last line, where we try to unify `bool -> bool` with `A -> ?1` and fail.

Well our intuition is mostly correct, but turns out we need to ensure that expressions we generalize don't contain `ref <exp>` *anywhere* in their body. In our case, we can safely generalize *any* expression that is a constant (`EBool`), variable (`EVar`), lambda (`ELam`), or a record literal (`ERecord`) whose elements are all generalizable. Everything else, like a function application, if expression, record projection, or let binding, we won't generalize.

This is called the *syntactic* value restriction. It is the criterion Standard ML uses to handle mutability. We are basically ensuring that we only generalize *values*, but take a conservative approach and define value as any constant, variable, lambda, or record literal whose elements are all values.

There are other approaches here, including OCaml's that does a deeper syntactic check to allow nested let bindings, record projection, some lambda applications, etc... Other approaches include changing our evaluation model from eager to lazy, analyzing the bodies of functions being applied to see if there are observable side effects, using an effect system to track effects of expressions, etc... That last one (which Koka employs) is kind of the ultimate solution to the problem, because we get precise tracking at the type-level for expressions that don't perform side effects and can be generalized. However, discussing effect systems is outside the scope of this article, and restricting generalization to syntactic values turns out to not be a problem in practice.

> Aside: Stephen Dolan recently took a different approach in [Rethinking the Value Restriction](https://www.youtube.com/watch?v=C1g_PO_xcI8) that supports full rank-1 types in ML, restricts generalization to lambda abstractions, and lazily instantiates foralls only when forced to by application or projection. There is some nuance around covariance annotations and curried functions, but consider taking a look at this talk!

Let's take a look at how we can modify `infer` to implement the value restriction. We'll start with `is_value`, a helper that determines if a typed expression is syntactically a value.

```ocaml
let rec is_value (x: texp) : bool =
    match x with
    | TEBool _ | TEVar _ | TELam _ -> true
    | TERecord (rec_lit, _) -> List.for_all rec_lit ~f:(fun (_, fld) -> is_value fld)
    | TEWith _ | TEApp _ | TEIf _ | TEProj _ | TELet _ | TELetRec _ -> false
```
The only interesting case is `TERecord`, where we check that all of its fields are also values.

Next, let's write `generalize_if_value`, a helper that wraps `gen` so we only generalize when the `rhs` is a value. Otherwise, we fall back to `dont_generalize`.

```ocaml
let generalize_if_value rhs : generic_ty =
    if is_value rhs then gen (typ rhs)
    else dont_generalize (typ rhs)
```

Now in our `ELet` case, the `None` branch where we previously called `gen (typ rhs)` becomes:

```ocaml
| None -> generalize_if_value rhs
```

The `ELetRec` case gets the same treatment in the `List.map` that produces `generalized_bindings`. The `None` branch where we previously called `gen (typ rhs)` becomes:

```ocaml
| None -> generalize_if_value rhs
```

Putting this all together, we have implemented the value restriction. If we added `ref`, `deref`, and `update` built-ins, our language would correctly handle mutability.

> Aside: Given the `is_value` predicate we defined in this section, the typing rules for let and let-rec are updated to generalize only when the rhs is a value.
> 
> ```
>                                 Γ ⊢ rhs : A                          
>       ---------------------------------------------------------------
>        vars = FV(A) \ FV(Γ)    constraints = { a :: R_a | a ∈ vars } 
>       ---------------------------------------------------------------
> T-Let:      S = ∀ vars. constraints => A if is_value(rhs) else A     
>       ---------------------------------------------------------------
>                         Γ, VarBind(x, S) ⊢ body : B                  
>       ---------------------------------------------------------------
>                         Γ ⊢ let x = rhs in body : B                  
> ```
> 
> ```
>                                            Γ_rec = Γ, { VarBind(x, A_x) | x ∈ decls }                                 
>          -------------------------------------------------------------------------------------------------------------
>           vars_x = FV(A_x) \ FV(Γ) for each x ∈ decls    constraints_x = { a :: R_a | a ∈ vars_x } for each x ∈ decls 
>          -------------------------------------------------------------------------------------------------------------
> T-LetRec:             S_x = ∀ vars_x. constraints_x => A_x if is_value(rhs_x) else A_x, for each x ∈ decls            
>          -------------------------------------------------------------------------------------------------------------
>           Γ_rec ⊢ rhs_x : A_x for each x ∈ decls                        Γ, { VarBind(x, S_x) | x ∈ decls } ⊢ body : B 
>          -------------------------------------------------------------------------------------------------------------
>                                        Γ ⊢ let rec { x = rhs_x | x ∈ decls } in body : B                              
> ```

Let's take a look at some examples.

You can find and run these examples in [lib/nine.ml](lib/nine.ml).

### Examples

We can simulate the example from before with our type-checker. We add definitions and signatures for `Ref`, `ref`, `deref`, and `update`. We can't really implement `update` without an actual memory store, so we just return an empty `Unit` record.

Because of the value restriction, `r` doesn't get generalized, and so `update` knows the type in the ref is just `bool -> bool`. When we try to apply the dereferenced value to a `Unit`, it now fails to typecheck as expected.
```ocaml
typecheck_source {|
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
```
Output: `UnificationFailure "failed to unify type bool with Unit"`

And here's how it looks being used successfully.
```ocaml
typecheck_source {|
    type Ref 'a = { value : 'a }
    type Unit = {}
    let ref : forall 'a. 'a -> Ref 'a = fun x -> { value = x } in
    let deref : forall 'a. Ref 'a -> 'a = fun r -> r.value in
    let update : forall 'a. Ref 'a -> 'a -> Unit = fun r -> fun x -> {} in
    let r = ref (fun x -> x) in
    let _ = update r (fun x -> if x then false else true) in
    update r (fun x -> false)
|}
```
Output: `Unit`

## Conclusion

The features covered in this article already give you a very sound and flexible system to program in, with generics, row polymorphism, side effects, and annotation-less type safety. As mentioned, see the companion repository https://github.com/smasher164/hm_tut for the source corresponding to each section. In the next post, we'll cover how to implement typeclasses/traits and their various extensions.