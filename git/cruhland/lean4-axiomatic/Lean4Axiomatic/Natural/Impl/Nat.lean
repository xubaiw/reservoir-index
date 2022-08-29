import Lean4Axiomatic.Natural
import Lean4Axiomatic.Natural.Impl.Generic

/-!
# Full implementation of `Natural` for Lean's prelude `Nat`
-/

namespace Lean4Axiomatic.Natural.Impl.Nat

local instance constructors : Constructors Nat := {
  zero := Nat.zero
  step := Nat.succ
}

local instance eqvOp? : Relation.Equivalence.EqvOp? Nat := {
  tildeDash := Eq
  refl := λ {x} => Eq.refl x
  symm := Eq.symm
  trans := Eq.trans
  tildeDashQuestion := Nat.decEq
}

local instance equality : Equality Nat := {
  eqvOp? := eqvOp?
}

local instance literals : Literals Nat := {
  literal := @instOfNatNat
  literal_zero := Rel.refl
  literal_step := Rel.refl
}

local instance step_substitutive
    : AA.Substitutive₁ (step : Nat → Nat) (· ≃ ·) (· ≃ ·)
    := {
  subst₁ := congrArg step
}

local instance core : Core Nat := {
  step_substitutive := step_substitutive
}

theorem succ_injective {n m : Nat} : Nat.succ n = Nat.succ m → n = m
| Eq.refl _ => Eq.refl _

local instance step_injective
    : AA.Injective (step : Nat → Nat) (· ≃ ·) (· ≃ ·)
    := {
  inject := succ_injective
}

def ind
    {motive : Nat → Sort v}
    (mz : motive 0) (ms : {n : Nat} → motive n → motive (Nat.succ n))
    : (n : Nat) → motive n
| Nat.zero => mz
| Nat.succ n => ms (ind mz ms n)

local instance axioms : Axioms Nat := {
  step_injective := step_injective
  step_neq_zero := Nat.noConfusion
  -- 2022-01-11: Using `Nat.rec` directly here, gives the following error:
  -- code generator does not support recursor 'Nat.rec' yet, consider using
  -- 'match ... with' and/or structural recursion
  ind := ind
}

local instance addition : Addition Nat := {
  addOp := _root_.instAddNat
  zero_add := @Nat.zero_add
  step_add := @Nat.succ_add
}

local instance multiplication : Multiplication Nat := {
  mulOp := _root_.instMulNat
  zero_mul := @Nat.zero_mul
  step_mul := @Nat.succ_mul
}

local instance exponentiation : Exponentiation Nat := {
  powOp := _root_.instPowNat
  pow_zero := rfl
  pow_step := rfl
}

instance : Natural Nat := {
  toCore := core
  toAxioms := axioms
  toAddition := addition
  toSign := Generic.sign
  toOrder := Generic.order
  toMultiplication := multiplication
  toExponentiation := exponentiation
}

end Lean4Axiomatic.Natural.Impl.Nat
