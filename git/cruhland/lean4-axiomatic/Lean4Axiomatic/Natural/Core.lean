import Lean4Axiomatic.AbstractAlgebra
import Lean4Axiomatic.Eqv

namespace Lean4Axiomatic.Natural

open Relation (EqvOp?)

/-!
# Fundamental definitions and properties of natural numbers

Closely follows the [Peano axioms](https://en.wikipedia.org/wiki/Peano_axioms).
-/

/--
Defines the primitive building blocks of all natural numbers.

Provides the first two Peano axioms; see `Axioms.Base` for the rest.
-/
class Constructors (ℕ : Type) where
  /--
  **Peano axiom 1**: `zero` is a natural number.

  We start at zero instead of one because it gives nicer algebraic properties;
  zero being the identity element for addition, for example.
  -/
  zero : ℕ

  /--
  **Peano axiom 2**: `step n` is a natural number for every natural number `n`.

  The intuition is that `step zero` represents the number one,
  `step (step zero)` represents two, `step (step (step zero))` is three, and in
  general `step n` is the next number after `n` when counting up.

  Other sources call this the _successor_ function, often abbreviated `S`,
  `suc`, or `succ`. Using `step` is just as short, and conveys a similar
  meaning, while not sounding like a word with negative connotations.
  -/
  step : ℕ → ℕ

export Constructors (zero step)

/-- Definitions pertaining to equality of natural number values. -/
class Equality (ℕ : Type) where
  /-- Natural numbers have a decidable equality relation. -/
  eqvOp? : EqvOp? ℕ

attribute [instance] Equality.eqvOp?

/-- Definitions pertaining to numeric literal support for natural numbers. -/
class Literals (ℕ : Type) [Constructors ℕ] [Equality ℕ] where
  /--
  Enables representation of natural numbers by numeric literals.

  Lean uses this instance to automatically replace literal values `n : Nat`
  with `OfNat.ofNat ℕ n` in expressions where `ℕ` is expected. For example, the
  raw literal `2` is represented as `succ (succ zero) : Nat`. In a context
  where `2` is expected to have type `ℕ`, Lean would use this instance to
  replace it with the term `OfNat.ofNat ℕ (succ (succ zero))`.

  The interpretation of this representation must be equivalent to the
  corresponding `Nat` values. The `literal_zero` and `literal_step` properties
  enforce this requirement.
  -/
  literal {n : Nat} : OfNat ℕ n

  /-- The numeric literal `0` represents the natural number `zero`. -/
  literal_zero : OfNat.ofNat (α := ℕ) Nat.zero ≃ zero

  /--
  If the numeric literal `ℓ : Nat` represents the natural number `k`, then the
  literal `Nat.succ ℓ` represents the natural number `step k`.
  -/
  literal_step {n : Nat}
    : OfNat.ofNat (α := ℕ) (Nat.succ n) ≃ step (OfNat.ofNat n)

attribute [instance default+1] Literals.literal

/--
Packages together the basic properties of natural numbers, to reduce the amount
of class references needed for more advanced properties.
-/
class Core (ℕ : Type) extends Constructors ℕ, Equality ℕ, Literals ℕ where
  /--
  The `step` function preserves equality of natural numbers; if two natural
  numbers are equal, they are still equal after `step` is applied to both.
   -/
  step_substitutive : AA.Substitutive (α := ℕ) step (· ≃ ·) (· ≃ ·)

attribute [instance] Core.step_substitutive

/--
Provides the remaining Peano axioms for natural numbers (see `Constructors`
for the first two).
-/
class Axioms.Base (ℕ : Type) [Core ℕ] where
  /-- **Peano axiom 3**: zero is not the successor of any natural number. -/
  step_neq_zero {n : ℕ} : step n ≄ 0

  /--
  **Peano axiom 4**: two natural numbers are equal if their successors are.
  -/
  step_injective : AA.Injective (α := ℕ) step (· ≃ ·) (· ≃ ·)

  /--
  **Peano axiom 5**: the principle of mathematical induction.

  Given a predicate on natural numbers (here named `motive`), assert that it
  holds of all natural numbers if the following criteria are met:
  1. (base case) `motive 0` holds;
  1. (inductive case) `motive (step n)` holds whenever `motive n` holds, for
     all `n : ℕ`.
  -/
  ind {motive : ℕ → Prop}
    : motive 0 → (∀ n, motive n → motive (step n)) → ∀ n, motive n

attribute [instance] Axioms.Base.step_injective

/-- Properties that follow from those provided in `Axioms.Base`. -/
class Axioms.Derived (ℕ : Type) [Core ℕ] extends Axioms.Base ℕ where
  /--
  Equivalent to `Axioms.Base.ind` but with a more convenient argument order
  when using the `apply` tactic.
  -/
  ind_on
    {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ m, motive m → motive (step m)) : motive n

  /--
  Similar to `ind_on`, but doesn't provide an inductive hypothesis. Useful for
  proofs that need a case split but not the full power of induction.
  -/
  cases_on
    {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ n, motive (step n)) : motive n

  /-- A natural number is never equal to its successor. -/
  step_neq {n : ℕ} : step n ≄ n

namespace Axioms
export Axioms.Base (ind step_injective step_neq_zero)
export Axioms.Derived (cases_on ind_on)
end Axioms

end Lean4Axiomatic.Natural
