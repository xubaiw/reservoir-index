# Expressions

Expressions (terms of type `Expr`) carry the data used to communicate with the
Lean kernel for core tasks such as type inference and definitional equality
checks.

In Lean, terms and types are represented by expressions. For instance, let's
consider `1` of type `Nat`. The type `Nat` is represented as a constant with the
name "Nat". And then `1` is an application of the function `Nat.succ` to the
term `Nat.zero`, so all this is represented as an application, given a constant
named "Nat.succ" and a constant named "Nat.zero".

That example gives us an idea of what we're aiming at: we use expressions to
represent all Lean terms at the meta level. Let's check the precise definition
of [`Expr`](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean).

```lean
import Lean

namespace Playground

inductive Expr where
  | bvar    : Nat → Expr                              -- bound variables
  | fvar    : FVarId → Expr                           -- free variables
  | mvar    : MVarId → Expr                           -- meta variables
  | sort    : Level → Expr                            -- Sort
  | const   : Name → List Level → Expr                -- constants
  | app     : Expr → Expr → Expr                      -- application
  | lam     : Name → Expr → Expr → BinderInfo → Expr  -- lambda abstraction
  | forallE : Name → Expr → Expr → BinderInfo → Expr  -- (dependent) arrow
  | letE    : Name → Expr → Expr → Expr → Bool → Expr -- let expressions
  -- less essential constructors:
  | lit     : Literal → Expr                          -- literals
  | mdata   : MData → Expr → Expr                     -- metadata
  | proj    : Name → Nat → Expr → Expr                -- projection

end Playground
```

What is each of these constructors doing?

- `bvar` is a __bound variable__. For example, the `x` in `fun x => x + 2` or
  `∑ x, x²`. This is any occurrence of a variable in an expression where there
  is a binder above it. Why is the argument a `Nat`? This is called a de-Bruijn
  index and will be explained ahead. You can figure out the type of a bound
  variable by looking at its binder, since the binder always has the type
  information for it.
- `fvar` is a __free variable__. These are variables which are not bound by a
  binder. An example is `x` in `x + 2`. Note that you can't just look at a free
  variable `x` and tell what its type is, there needs to be a context
  which contains a declaration for `x` and its type. A free variable has an ID
  that tells you where to look for it in a `LocalContext`. In Lean 3, free
  variables were called "local constants" or "locals".
- `mvar` is a __metavariable__. There will be much more on these later, but you
  can think of it as a placeholder or a 'hole' in an expression that needs to be
  filled at a later point.
- `sort` is used for `Type u`, `Prop` etc.
- `const` is a constant that has been defined earlier in the Lean document.
- `app` is a function application. Multiple arguments are done using _partial
  application_: `f x y ↝ app (app f x) y`.
- `lam n t b` is a lambda expression (`fun ($n : $t) => $b`). The `b` argument
  is called the __body__. Note that you have to give the type of the variable
  you are binding.
- `forallE n t b` is a dependent arrow expression (`($n : $t) → $b`). This is
  also sometimes called a Π-type or Π-expression. Note that the non-dependent
  arrow `α → β` is a special case of `(a : α) → β` where `β` doesn't depend on
  `a`. The `E` on the end of `forallE` is to distinguish it from the `forall`
  keyword.
- `letE n t v b` is a __let binder__ (`let ($n : $t) := $v in $b`).
- `lit` is a __literal__, this is a number or string literal like `4` or
  `"hello world"`. These are not strictly necessary for the kernel, but they are
  kept mainly for convenience. (Ie in Lean 3, there were a load of tricks needed
  to store `11234 : Nat` as something more efficient than
  `succ $ succ $ succ ... $ succ zero`)
- `mdata` is just a way of storing extra information on expressions that might
  be useful, without changing the nature of the expression.
- `proj` is for projection. Suppose you have a structure such as `p : α × β`,
  rather than storing the projection `π₁ p` as `app π₁ p`, it is expressed as
  `proj Prod 0 p`. This is for efficiency reasons ([todo] find link to docstring
  explaining this).

## de-Bruijn Indexes

Consider the following lambda expression ` (λ f x => f x x) (λ x y => x + y) 5`,
we have to be very careful when we reduce this, because we get a clash in the
variable `x`.

To avoid variable name-clash carnage, `Expr`s use a nifty trick called
__de-Bruijn indexes__. In de-Bruijn indexing, each variable bound by a `lam` or
a `forallE` is converted into a number `#n`. The number says how many binders up
the `Expr` tree we should look to find the binder which binds this variable.
So our above example would become (putting wildcards `_` in the type arguments
for now for brevity):
``app (app (lam `f _ (lam `x _ (app (app #1 #0) #0))) (lam `x _ (lam `y _ (app (app plus #1) #0)))) five``
Now we don't need to rename variables when we perform β-reduction. We also
really easily check if two `Expr`s containing bound expressions are equal.

This is why the signature of the `bvar` case is `Nat → Expr` and not
`Name → Expr`. If in our `Expr`, all `bvar`s are bound, we say that the `Expr`
is __closed__. The process of replacing all instances of an unbound `bvar` with
an `Expr` is called __instantiation__. Going the other way is called
__abstraction__.

## Constructing Expressions

The simplest expressions we can construct are constants. We use `mkConst`
with argument a name. Below are two examples of this, both giving an expression
for the natural number `0`. 

The second form (with double backticks) is better, as it resolves the name to a
global name, checking, in the process that it is valid.

```lean
open Lean

def z' := mkConst `Nat.zero
#eval z' -- Lean.Expr.const `Nat.zero []

def z := mkConst ``Nat.zero
#eval z -- Lean.Expr.const `Nat.zero []
```

To illustrate the difference, here are two further examples. The first
definition is unsafe as it is not valid without `open Nat` in the context. On
the other hand, the second resolves correctly.

```lean
open Nat

def z₁ := mkConst `zero
#eval z₁ -- Lean.Expr.const `zero []

def z₂ := mkConst ``zero
#eval z₂ -- Lean.Expr.const `Nat.zero []
```

The next class of expressions we consider are function applications. These
can be built using `mkApp` with the first argument being an expression for the
function and the second being an expression for the argument.

Here are two examples. The first is simply a constant applied to another. The
second is a recursive definition giving an expression as a function of a natural
number.

```lean
def one := mkApp (mkConst ``Nat.succ) z
#eval one
-- Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero [])

def natExpr: Nat → Expr 
| 0     => z
| n + 1 => mkApp (mkConst ``Nat.succ) (natExpr n)
```

Next we use the variant `mkAppN` which allows application with multiple
arguments.

```lean
def sumExpr : Nat → Nat → Expr 
| n, m => mkAppN (mkConst ``Nat.add) #[natExpr n, natExpr m]
```

As you may have noticed, we didn't show `#eval` outputs for the two last
functions. That's because the resulting expressions can grow so large that it's
hard to make sense of them.

We next consider the helper `mkLambda` to construct a simple function which
takes any natural number `x` and returns `Nat.zero`. The argument
`BinderInfo.default` for the constructor says that `x` is explicit.

```lean
def constZero : Expr := 
  mkLambda `x BinderInfo.default (mkConst ``Nat) (mkConst ``Nat.zero)

#eval constZero
-- Lean.Expr.lam `x (Lean.Expr.const `Nat []) (Lean.Expr.const `Nat.zero [])
--   (Lean.BinderInfo.default)
```

In the next chapter we shall explore some functions that compute in the
`MetaM` monad, opening room for more powerful tricks involving expressions.
