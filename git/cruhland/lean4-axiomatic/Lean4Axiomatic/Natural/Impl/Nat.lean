import Lean4Axiomatic.Natural
import Lean4Axiomatic.Natural.Impl.Default
import Lean4Axiomatic.Natural.Impl.Derived

namespace Lean4Axiomatic.Natural.Impl.Nat

instance constructors : Constructors Nat := {
  zero := Nat.zero
  step := Nat.succ
}

instance eqvOp? : Relation.Equivalence.EqvOp? Nat := {
  tildeDash := Eq
  refl := λ {x} => Eq.refl x
  symm := Eq.symm
  trans := Eq.trans
  tildeDashQuestion := Nat.decEq
}

instance equality : Equality Nat := {
  eqvOp? := eqvOp?
}

instance literals : Literals Nat := {
  literal := @instOfNatNat
  literal_zero := Rel.refl
  literal_step := Rel.refl
}

instance step_substitutive
    : AA.Substitutive₁ (step : Nat → Nat) (· ≃ ·) (· ≃ ·)
    := {
  subst₁ := congrArg step
}

instance core : Core Nat := {
  step_substitutive := step_substitutive
}

theorem succ_injective {n m : Nat} : Nat.succ n = Nat.succ m → n = m
| Eq.refl _ => Eq.refl _

instance step_injective : AA.Injective (step : Nat → Nat) (· ≃ ·) (· ≃ ·) := {
  inject := succ_injective
}

def ind
    {motive : Nat → Sort v}
    (mz : motive 0) (ms : {n : Nat} → motive n → motive (Nat.succ n))
    : (n : Nat) → motive n
| Nat.zero => mz
| Nat.succ n => ms (ind mz ms n)

instance axioms : Axioms Nat := {
  step_injective := step_injective
  step_neq_zero := Nat.noConfusion
  -- 2022-01-11: Using `Nat.rec` directly here, gives the following error:
  -- code generator does not support recursor 'Nat.rec' yet, consider using
  -- 'match ... with' and/or structural recursion
  ind := ind
}

instance addition_base : Addition.Base Nat := {
  addOp := _root_.instAddNat
  zero_add := @Nat.zero_add
  step_add := @Nat.succ_add
}

instance multiplication_base : Multiplication.Base Nat := {
  mulOp := _root_.instMulNat
  zero_mul := @Nat.zero_mul
  step_mul := @Nat.succ_mul
}

instance exponentiation_base : Exponentiation.Base Nat := {
  powOp := _root_.instPowNatNat
  pow_zero := rfl
  pow_step := rfl
}

instance : Natural Nat where
  toCore := core
  toAxioms := axioms
  toAddition := Natural.Derived.addition_derived
  toSign := Natural.Default.sign
  toOrder := Natural.Derived.order_derived
  toMultiplication := Natural.Derived.multiplication_derived
  toExponentiation := exponentiation_base

end Lean4Axiomatic.Natural.Impl.Nat
