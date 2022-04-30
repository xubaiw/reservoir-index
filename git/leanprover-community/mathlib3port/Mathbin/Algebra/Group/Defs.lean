/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Mathbin.Algebra.Group.ToAdditive
import Mathbin.Tactic.Basic

/-!
# Typeclasses for (semi)groups and monoids

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(add_)?(comm_)?(semigroup|monoid|group)`, where `add_` means that
the class uses additive notation and `comm_` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `algebra.group.basic`.

We also introduce notation classes `has_scalar` and `has_vadd` for multiplicative and additive
actions and register the following instances:

- `has_pow M ℕ`, for monoids `M`, and `has_pow G ℤ` for groups `G`;
- `has_scalar ℕ M` for additive monoids `M`, and `has_scalar ℤ G` for additive groups `G`.

## Notation

- `+`, `-`, `*`, `/`, `^` : the usual arithmetic operations; the underlying functions are
  `has_add.add`, `has_neg.neg`/`has_sub.sub`, `has_mul.mul`, `has_div.div`, and `has_pow.pow`.
- `a • b` is used as notation for `has_scalar.smul a b`.
- `a +ᵥ b` is used as notation for `has_vadd.vadd a b`.

-/


/-- Type class for the `+ᵥ` notation. -/
class HasVadd (G : Type _) (P : Type _) where
  vadd : G → P → P

/-- Type class for the `-ᵥ` notation. -/
class HasVsub (G : outParam (Type _)) (P : Type _) where
  vsub : P → P → G

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
@[ext, to_additive HasVadd]
class HasScalar (M : Type _) (α : Type _) where
  smul : M → α → α

-- mathport name: «expr +ᵥ »
infixl:65 " +ᵥ " => HasVadd.vadd

-- mathport name: «expr -ᵥ »
infixl:65 " -ᵥ " => HasVsub.vsub

-- mathport name: «expr • »
infixr:73 " • " => HasScalar.smul

attribute [to_additive_reorder 1] Pow

attribute [to_additive_reorder 1 4] Pow.pow

attribute [to_additive HasScalar] Pow

attribute [to_additive HasScalar.smul] Pow.pow

universe u

/- Additive "sister" structures.
   Example, add_semigroup mirrors semigroup.
   These structures exist just to help automation.
   In an alternative design, we could have the binary operation as an
   extra argument for semigroup, monoid, group, etc. However, the lemmas
   would be hard to index since they would not contain any constant.
   For example, mul_assoc would be

   lemma mul_assoc {α : Type u} {op : α → α → α} [semigroup α op] :
                   ∀ a b c : α, op (op a b) c = op a (op b c) :=
    semigroup.mul_assoc

   The simplifier cannot effectively use this lemma since the pattern for
   the left-hand-side would be

        ?op (?op ?a ?b) ?c

   Remark: we use a tactic for transporting theorems from the multiplicative fragment
   to the additive one.
-/
mk_simp_attribute field_simps :=
  "The simpset `field_simps` is used by the tactic `field_simp` to\nreduce an expression in a field to an expression of the form `n / d` where `n` and `d` are\ndivision-free."

section Mul

variable {G : Type u} [Mul G]

/-- `left_mul g` denotes left multiplication by `g` -/
@[to_additive "`left_add g` denotes left addition by `g`"]
def leftMul : G → G → G := fun g : G => fun x : G => g * x

/-- `right_mul g` denotes right multiplication by `g` -/
@[to_additive "`right_add g` denotes right addition by `g`"]
def rightMul : G → G → G := fun g : G => fun x : G => x * g

end Mul

/-- A semigroup is a type with an associative `(*)`. -/
@[protect_proj, ancestor Mul, ext]
class Semigroupₓ (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

/-- An additive semigroup is a type with an associative `(+)`. -/
@[protect_proj, ancestor Add, ext]
class AddSemigroupₓ (G : Type u) extends Add G where
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

attribute [to_additive] Semigroupₓ

section Semigroupₓ

variable {G : Type u} [Semigroupₓ G]

@[no_rsimp, to_additive]
theorem mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
  Semigroupₓ.mul_assoc

@[to_additive]
instance Semigroupₓ.to_is_associative : IsAssociative G (· * ·) :=
  ⟨mul_assoc⟩

end Semigroupₓ

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[protect_proj, ancestor Semigroupₓ, ext]
class CommSemigroupₓ (G : Type u) extends Semigroupₓ G where
  mul_comm : ∀ a b : G, a * b = b * a

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[protect_proj, ancestor AddSemigroupₓ, ext]
class AddCommSemigroupₓ (G : Type u) extends AddSemigroupₓ G where
  add_comm : ∀ a b : G, a + b = b + a

attribute [to_additive] CommSemigroupₓ

section CommSemigroupₓ

variable {G : Type u} [CommSemigroupₓ G]

@[no_rsimp, to_additive]
theorem mul_comm : ∀ a b : G, a * b = b * a :=
  CommSemigroupₓ.mul_comm

@[to_additive]
instance CommSemigroupₓ.to_is_commutative : IsCommutative G (· * ·) :=
  ⟨mul_comm⟩

end CommSemigroupₓ

/-- A `left_cancel_semigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[protect_proj, ancestor Semigroupₓ, ext]
class LeftCancelSemigroup (G : Type u) extends Semigroupₓ G where
  mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c

/-- An `add_left_cancel_semigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[protect_proj, ancestor AddSemigroupₓ, ext]
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroupₓ G where
  add_left_cancel : ∀ a b c : G, a + b = a + c → b = c

attribute [to_additive AddLeftCancelSemigroup] LeftCancelSemigroup

section LeftCancelSemigroup

variable {G : Type u} [LeftCancelSemigroup G] {a b c : G}

@[to_additive]
theorem mul_left_cancelₓ : a * b = a * c → b = c :=
  LeftCancelSemigroup.mul_left_cancel a b c

@[to_additive]
theorem mul_left_cancel_iffₓ : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancelₓ, congr_argₓ _⟩

@[to_additive]
theorem mul_right_injective (a : G) : Function.Injective ((· * ·) a) := fun b c => mul_left_cancelₓ

@[simp, to_additive]
theorem mul_right_injₓ (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff

end LeftCancelSemigroup

/-- A `right_cancel_semigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[protect_proj, ancestor Semigroupₓ, ext]
class RightCancelSemigroup (G : Type u) extends Semigroupₓ G where
  mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c

/-- An `add_right_cancel_semigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[protect_proj, ancestor AddSemigroupₓ, ext]
class AddRightCancelSemigroup (G : Type u) extends AddSemigroupₓ G where
  add_right_cancel : ∀ a b c : G, a + b = c + b → a = c

attribute [to_additive AddRightCancelSemigroup] RightCancelSemigroup

section RightCancelSemigroup

variable {G : Type u} [RightCancelSemigroup G] {a b c : G}

@[to_additive]
theorem mul_right_cancelₓ : a * b = c * b → a = c :=
  RightCancelSemigroup.mul_right_cancel a b c

@[to_additive]
theorem mul_right_cancel_iffₓ : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancelₓ, congr_argₓ _⟩

@[to_additive]
theorem mul_left_injective (a : G) : Function.Injective fun x => x * a := fun b c => mul_right_cancelₓ

@[simp, to_additive]
theorem mul_left_injₓ (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective a).ne_iff

end RightCancelSemigroup

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
@[ancestor One Mul]
class MulOneClassₓ (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
@[ancestor Zero Add]
class AddZeroClass (M : Type u) extends Zero M, Add M where
  zero_add : ∀ a : M, 0 + a = a
  add_zero : ∀ a : M, a + 0 = a

attribute [to_additive] MulOneClassₓ

@[ext, to_additive]
theorem MulOneClassₓ.ext {M : Type u} : ∀ ⦃m₁ m₂ : MulOneClassₓ M⦄, m₁.mul = m₂.mul → m₁ = m₂ := by
  rintro ⟨one₁, mul₁, one_mul₁, mul_one₁⟩ ⟨one₂, mul₂, one_mul₂, mul_one₂⟩ (rfl : mul₁ = mul₂)
  congr
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)

section MulOneClassₓ

variable {M : Type u} [MulOneClassₓ M]

@[ematch, simp, to_additive]
theorem one_mulₓ : ∀ a : M, 1 * a = a :=
  MulOneClassₓ.one_mul

@[ematch, simp, to_additive]
theorem mul_oneₓ : ∀ a : M, a * 1 = a :=
  MulOneClassₓ.mul_one

@[to_additive]
instance MulOneClassₓ.to_is_left_id : IsLeftId M (· * ·) 1 :=
  ⟨MulOneClassₓ.one_mul⟩

@[to_additive]
instance MulOneClassₓ.to_is_right_id : IsRightId M (· * ·) 1 :=
  ⟨MulOneClassₓ.mul_one⟩

end MulOneClassₓ

section

variable {M : Type u}

/-- The fundamental power operation in a monoid. `npow_rec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
-- use `x * npow_rec n x` and not `npow_rec n x * x` in the definition to make sure that
-- definitional unfolding of `npow_rec` is blocked, to avoid deep recursion issues.
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, a => 1
  | n + 1, a => a * npowRec n a

/-- The fundamental scalar multiplication in an additive monoid. `nsmul_rec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmulRec [Zero M] [Add M] : ℕ → M → M
  | 0, a => 0
  | n + 1, a => a + nsmulRec n a

attribute [to_additive] npowRec

end

library_note "forgetful inheritance"/--
Suppose that one can put two mathematical structures on a type, a rich one `R` and a poor one
`P`, and that one can deduce the poor structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = metric_space` and `P = topological_space`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `metric_space` / `topological_space`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `topological_space`
instances on the product. This is not compatible with the way instances are designed and used:
there should be at most one instance of a kind on each type. This approach has created an instance
diamond that does not commute definitionally.

The second approach solves this issue. Now, a metric space contains both a distance, a topology, and
a proof that the topology coincides with the one coming from the distance. When one defines the
product of two metric spaces, one uses the sup distance and the product topology, and one has to
give the proof that the sup distance induces the product topology. Following both sides of the
instance diamond then gives rise (definitionally) to the product topology on the product space.

Another approach would be to have the rich type class take the poor type class as an instance
parameter. It would solve the diamond problem, but it would lead to a blow up of the number
of type classes one would need to declare to work with complicated classes, say a real inner
product space, and would create exponential complexity when working with products of
such complicated spaces, that are avoided by bundling things carefully as above.

Note that this description of this specific case of the product of metric spaces is oversimplified
compared to mathlib, as there is an intermediate typeclass between `metric_space` and
`topological_space` called `uniform_space`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
structure with fewer fields, where the helper function fills the remaining fields. See for instance
`uniform_space.of_core` or `real_inner_product.of_core`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/


-- ././Mathport/Syntax/Translate/Basic.lean:915:4: warning: unsupported (TODO): `[tacs]
/-- `try_refl_tac` solves goals of the form `∀ a b, f a b = g a b`,
if they hold by definition. -/
unsafe def try_refl_tac : tactic Unit :=
  sorry

/-!
### Design note on `add_monoid` and `monoid`

An `add_monoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`polynomial R` has a natural `R`-action defined by multiplication on the coefficients. This means
that `polynomial ℕ` would have two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself).

To solve this issue, we embed an `ℕ`-action in the definition of an `add_monoid` (which is by
default equal to the naive action `a + ... + a`, but can be adjusted when needed), and declare
a `has_scalar ℕ α` instance using this action. See Note [forgetful inheritance] for more
explanations on this pattern.

For example, when we define `polynomial R`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `add_monoid`). In this way, the two natural `has_scalar ℕ (polynomial ℕ)` instances are defeq.

The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.

A basic theory for the power function on monoids and the `ℕ`-action on additive monoids is built in
the file `algebra.group_power.basic`. For now, we only register the most basic properties that we
need right away.

In the definition, we use `n.succ` instead of `n + 1` in the `nsmul_succ'` and `npow_succ'` fields
to make sure that `to_additive` is not confused (otherwise, it would try to convert `1 : ℕ`
to `0 : ℕ`).
-/


/-- An `add_monoid` is an `add_semigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
@[ancestor AddSemigroupₓ AddZeroClass]
class AddMonoidₓ (M : Type u) extends AddSemigroupₓ M, AddZeroClass M where
  nsmul : ℕ → M → M := nsmulRec
  nsmul_zero' : ∀ x, nsmul 0 x = 0 := by
    run_tac
      try_refl_tac
  nsmul_succ' : ∀ n : ℕ x, nsmul n.succ x = x + nsmul n x := by
    run_tac
      try_refl_tac

/-- A `monoid` is a `semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[ancestor Semigroupₓ MulOneClassₓ, to_additive]
class Monoidₓ (M : Type u) extends Semigroupₓ M, MulOneClassₓ M where
  npow : ℕ → M → M := npowRec
  npow_zero' : ∀ x, npow 0 x = 1 := by
    run_tac
      try_refl_tac
  npow_succ' : ∀ n : ℕ x, npow n.succ x = x * npow n x := by
    run_tac
      try_refl_tac

instance Monoidₓ.hasPow {M : Type _} [Monoidₓ M] : Pow M ℕ :=
  ⟨fun x n => Monoidₓ.npow n x⟩

instance AddMonoidₓ.hasScalarNat {M : Type _} [AddMonoidₓ M] : HasScalar ℕ M :=
  ⟨AddMonoidₓ.nsmul⟩

attribute [to_additive AddMonoidₓ.hasScalarNat] Monoidₓ.hasPow

section

variable {M : Type _} [Monoidₓ M]

@[simp, to_additive nsmul_eq_smul]
theorem npow_eq_powₓ (n : ℕ) (x : M) : Monoidₓ.npow n x = x ^ n :=
  rfl

-- the attributes are intentionally out of order. `zero_smul` proves `zero_nsmul`.
@[to_additive zero_nsmul, simp]
theorem pow_zeroₓ (a : M) : a ^ 0 = 1 :=
  Monoidₓ.npow_zero' _

@[to_additive succ_nsmul]
theorem pow_succₓ (a : M) (n : ℕ) : a ^ (n + 1) = a * a ^ n :=
  Monoidₓ.npow_succ' n a

end

section Monoidₓ

variable {M : Type u} [Monoidₓ M]

@[to_additive]
theorem left_inv_eq_right_invₓ {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mulₓ c, ← hba, mul_assoc, hac, mul_oneₓ b]

end Monoidₓ

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
@[protect_proj, ancestor AddMonoidₓ AddCommSemigroupₓ]
class AddCommMonoidₓ (M : Type u) extends AddMonoidₓ M, AddCommSemigroupₓ M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[protect_proj, ancestor Monoidₓ CommSemigroupₓ, to_additive]
class CommMonoidₓ (M : Type u) extends Monoidₓ M, CommSemigroupₓ M

section LeftCancelMonoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_left_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor AddLeftCancelSemigroup AddMonoidₓ]
class AddLeftCancelMonoid (M : Type u) extends AddLeftCancelSemigroup M, AddMonoidₓ M

/-- A monoid in which multiplication is left-cancellative. -/
@[protect_proj, ancestor LeftCancelSemigroup Monoidₓ, to_additive AddLeftCancelMonoid]
class LeftCancelMonoid (M : Type u) extends LeftCancelSemigroup M, Monoidₓ M

end LeftCancelMonoid

section RightCancelMonoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor AddRightCancelSemigroup AddMonoidₓ]
class AddRightCancelMonoid (M : Type u) extends AddRightCancelSemigroup M, AddMonoidₓ M

/-- A monoid in which multiplication is right-cancellative. -/
@[protect_proj, ancestor RightCancelSemigroup Monoidₓ, to_additive AddRightCancelMonoid]
class RightCancelMonoid (M : Type u) extends RightCancelSemigroup M, Monoidₓ M

end RightCancelMonoid

section CancelMonoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor AddLeftCancelMonoid AddRightCancelMonoid]
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M

/-- A monoid in which multiplication is cancellative. -/
@[protect_proj, ancestor LeftCancelMonoid RightCancelMonoid, to_additive AddCancelMonoid]
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M

/-- Commutative version of add_cancel_monoid. -/
@[protect_proj, ancestor AddLeftCancelMonoid AddCommMonoidₓ]
class AddCancelCommMonoid (M : Type u) extends AddLeftCancelMonoid M, AddCommMonoidₓ M

/-- Commutative version of cancel_monoid. -/
@[protect_proj, ancestor LeftCancelMonoid CommMonoidₓ, to_additive AddCancelCommMonoid]
class CancelCommMonoid (M : Type u) extends LeftCancelMonoid M, CommMonoidₓ M

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type u) [CancelCommMonoid M] : CancelMonoid M :=
  { ‹CancelCommMonoid M› with
    mul_right_cancel := fun a b c h =>
      mul_left_cancelₓ <| by
        rw [mul_comm, h, mul_comm] }

end CancelMonoid

/-- The fundamental power operation in a group. `zpow_rec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`,  which has better definitional behavior. -/
def zpowRec {M : Type _} [One M] [Mul M] [Inv M] : ℤ → M → M
  | Int.ofNat n, a => npowRec n a
  | -[1+ n], a => (npowRec n.succ a)⁻¹

/-- The fundamental scalar multiplication in an additive group. `zsmul_rec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def zsmulRec {M : Type _} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmulRec n a
  | -[1+ n], a => -nsmulRec n.succ a

attribute [to_additive] zpowRec

/-- A `div_inv_monoid` is a `monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This is the immediate common ancestor of `group` and `group_with_zero`,
in order to deduplicate the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no
`∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we
also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the
`(/)` coming from `group_with_zero_has_div` cannot be definitionally equal to
the `(/)` coming from `foo.has_div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
@[protect_proj, ancestor Monoidₓ Inv Div]
class DivInvMonoidₓ (G : Type u) extends Monoidₓ G, Inv G, Div G where
  div := fun a b => a * b⁻¹
  div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by
    run_tac
      try_refl_tac
  zpow : ℤ → G → G := zpowRec
  zpow_zero' : ∀ a : G, zpow 0 a = 1 := by
    run_tac
      try_refl_tac
  zpow_succ' : ∀ n : ℕ a : G, zpow (Int.ofNat n.succ) a = a * zpow (Int.ofNat n) a := by
    run_tac
      try_refl_tac
  zpow_neg' : ∀ n : ℕ a : G, zpow -[1+ n] a = (zpow n.succ a)⁻¹ := by
    run_tac
      try_refl_tac

/-- A `sub_neg_monoid` is an `add_monoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_sub (foo X)` instance but no
`∀ X, has_neg (foo X)`. Suppose we also have an instance
`∀ X [cromulent X], add_group (foo X)`. Then the `(-)` coming from
`add_group.has_sub` cannot be definitionally equal to the `(-)` coming from
`foo.has_sub`.

In the same way, adding a `zsmul` field makes it possible to avoid definitional failures
in diamonds. See the definition of `add_monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
@[protect_proj, ancestor AddMonoidₓ Neg Sub]
class SubNegMonoidₓ (G : Type u) extends AddMonoidₓ G, Neg G, Sub G where
  sub := fun a b => a + -b
  sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by
    run_tac
      try_refl_tac
  zsmul : ℤ → G → G := zsmulRec
  zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by
    run_tac
      try_refl_tac
  zsmul_succ' : ∀ n : ℕ a : G, zsmul (Int.ofNat n.succ) a = a + zsmul (Int.ofNat n) a := by
    run_tac
      try_refl_tac
  zsmul_neg' : ∀ n : ℕ a : G, zsmul -[1+ n] a = -zsmul n.succ a := by
    run_tac
      try_refl_tac

attribute [to_additive SubNegMonoidₓ] DivInvMonoidₓ

instance DivInvMonoidₓ.hasPow {M} [DivInvMonoidₓ M] : Pow M ℤ :=
  ⟨fun x n => DivInvMonoidₓ.zpow n x⟩

instance SubNegMonoidₓ.hasScalarInt {M} [SubNegMonoidₓ M] : HasScalar ℤ M :=
  ⟨SubNegMonoidₓ.zsmul⟩

attribute [to_additive SubNegMonoidₓ.hasScalarInt] DivInvMonoidₓ.hasPow

section

variable {G : Type _} [DivInvMonoidₓ G]

@[simp, to_additive zsmul_eq_smul]
theorem zpow_eq_pow (n : ℤ) (x : G) : DivInvMonoidₓ.zpow n x = x ^ n :=
  rfl

@[simp, to_additive zero_zsmul]
theorem zpow_zero (a : G) : a ^ (0 : ℤ) = 1 :=
  DivInvMonoidₓ.zpow_zero' a

@[simp, norm_cast, to_additive coe_nat_zsmul]
theorem zpow_coe_nat (a : G) : ∀ n : ℕ, a ^ (n : ℤ) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zeroₓ _).symm
  | n + 1 =>
    calc
      a ^ (↑(n + 1) : ℤ) = a * a ^ (n : ℤ) := DivInvMonoidₓ.zpow_succ' _ _
      _ = a * a ^ n := congr_argₓ ((· * ·) a) (zpow_coe_nat n)
      _ = a ^ (n + 1) := (pow_succₓ _ _).symm
      

@[to_additive of_nat_zsmul]
theorem zpow_of_nat (a : G) (n : ℕ) : a ^ Int.ofNat n = a ^ n :=
  zpow_coe_nat a n

@[simp, to_additive]
theorem zpow_neg_succ_of_nat (a : G) (n : ℕ) : a ^ -[1+ n] = (a ^ (n + 1))⁻¹ := by
  rw [← zpow_coe_nat]
  exact DivInvMonoidₓ.zpow_neg' n a

end

@[to_additive]
theorem div_eq_mul_inv {G : Type u} [DivInvMonoidₓ G] : ∀ a b : G, a / b = a * b⁻¹ :=
  DivInvMonoidₓ.div_eq_mul_inv

section

-- ././Mathport/Syntax/Translate/Basic.lean:210:40: warning: unsupported option extends_priority
-- ensure that we don't go via these typeclasses to find `has_inv` on groups and groups with zero
set_option extends_priority 50

/-- Auxiliary typeclass for types with an involutive `has_inv`. -/
@[ancestor Inv]
class HasInvolutiveInv (G : Type _) extends Inv G where
  inv_inv : ∀ x : G, x⁻¹⁻¹ = x

/-- Auxiliary typeclass for types with an involutive `has_neg`. -/
@[ancestor Neg]
class HasInvolutiveNeg (A : Type _) extends Neg A where
  neg_neg : ∀ x : A, - -x = x

attribute [to_additive] HasInvolutiveInv

end

section HasInvolutiveInv

variable {G : Type _} [HasInvolutiveInv G]

@[simp, to_additive]
theorem inv_invₓ (a : G) : a⁻¹⁻¹ = a :=
  HasInvolutiveInv.inv_inv _

end HasInvolutiveInv

/-- A `group` is a `monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.
-/
@[protect_proj, ancestor DivInvMonoidₓ]
class Groupₓ (G : Type u) extends DivInvMonoidₓ G where
  mul_left_inv : ∀ a : G, a⁻¹ * a = 1

/-- An `add_group` is an `add_monoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.
-/
@[protect_proj, ancestor SubNegMonoidₓ]
class AddGroupₓ (A : Type u) extends SubNegMonoidₓ A where
  add_left_neg : ∀ a : A, -a + a = 0

attribute [to_additive] Groupₓ

/-- Abbreviation for `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.

Useful because it corresponds to the fact that `Grp` is a subcategory of `Mon`.
Not an instance since it duplicates `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "Abbreviation for `@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`.\n\nUseful because it corresponds to the fact that `AddGroup` is a subcategory of `AddMon`.\nNot an instance since it duplicates\n`@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`."]
def Groupₓ.toMonoid (G : Type u) [Groupₓ G] : Monoidₓ G :=
  @DivInvMonoidₓ.toMonoid _ (@Groupₓ.toDivInvMonoid _ _)

section Groupₓ

variable {G : Type u} [Groupₓ G] {a b c : G}

@[simp, to_additive]
theorem mul_left_invₓ : ∀ a : G, a⁻¹ * a = 1 :=
  Groupₓ.mul_left_inv

@[to_additive]
theorem inv_mul_selfₓ (a : G) : a⁻¹ * a = 1 :=
  mul_left_invₓ a

@[simp, to_additive]
theorem inv_mul_cancel_leftₓ (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, mul_left_invₓ, one_mulₓ]

@[simp, to_additive]
theorem inv_eq_of_mul_eq_oneₓ (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_invₓ (inv_mul_selfₓ a) h

@[to_additive]
instance (priority := 100) Groupₓ.toHasInvolutiveInv : HasInvolutiveInv G where
  inv := Inv.inv
  inv_inv := fun a => inv_eq_of_mul_eq_oneₓ (mul_left_invₓ a)

@[simp, to_additive]
theorem mul_right_invₓ (a : G) : a * a⁻¹ = 1 := by
  have : a⁻¹⁻¹ * a⁻¹ = 1 := mul_left_invₓ a⁻¹
  rwa [inv_invₓ] at this

@[to_additive]
theorem mul_inv_selfₓ (a : G) : a * a⁻¹ = 1 :=
  mul_right_invₓ a

@[simp, to_additive]
theorem mul_inv_cancel_rightₓ (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_right_invₓ, mul_oneₓ]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Groupₓ.toCancelMonoid : CancelMonoid G :=
  { ‹Groupₓ G› with
    mul_right_cancel := fun a b c h => by
      rw [← mul_inv_cancel_rightₓ a b, h, mul_inv_cancel_rightₓ],
    mul_left_cancel := fun a b c h => by
      rw [← inv_mul_cancel_leftₓ a b, h, inv_mul_cancel_leftₓ] }

end Groupₓ

@[to_additive]
theorem Groupₓ.to_div_inv_monoid_injective {G : Type _} : Function.Injective (@Groupₓ.toDivInvMonoid G) := by
  rintro ⟨⟩ ⟨⟩ h
  replace h := DivInvMonoidₓ.mk.inj h
  dsimp  at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

/-- A commutative group is a group with commutative `(*)`. -/
@[protect_proj, ancestor Groupₓ CommMonoidₓ]
class CommGroupₓ (G : Type u) extends Groupₓ G, CommMonoidₓ G

/-- An additive commutative group is an additive group with commutative `(+)`. -/
@[protect_proj, ancestor AddGroupₓ AddCommMonoidₓ]
class AddCommGroupₓ (G : Type u) extends AddGroupₓ G, AddCommMonoidₓ G

attribute [to_additive] CommGroupₓ

attribute [instance] AddCommGroupₓ.toAddCommMonoid

@[to_additive]
theorem CommGroupₓ.to_group_injective {G : Type u} : Function.Injective (@CommGroupₓ.toGroup G) := by
  rintro ⟨⟩ ⟨⟩ h
  replace h := Groupₓ.mk.inj h
  dsimp  at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rfl

section CommGroupₓ

variable {G : Type u} [CommGroupₓ G]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroupₓ.toCancelCommMonoid : CancelCommMonoid G :=
  { ‹CommGroupₓ G›, Groupₓ.toCancelMonoid with }

end CommGroupₓ

