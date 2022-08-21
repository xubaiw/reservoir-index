import Lean4Axiomatic.Natural.Order

/-!
# Generic natural number axiom implementations

The term "generic" here means the implementations don't depend on the
implementation of the natural number type itself; i.e., they are generic, or
parameterized, over `ℕ`. Thus they can be used to provide part of a complete
implementation of `Natural`, no matter which concrete type is used for `ℕ`.
-/

namespace Lean4Axiomatic.Natural.Impl.Generic

variable {ℕ : Type}

section literals

variable [Constructors ℕ]
variable [Equality ℕ]

/--
Convert a `Nat` value to its equivalent `ℕ` value.

Lean's prelude defines `Nat` as its natural number type, so it's useful to have
a way to translate from it. In particular, numeric literals are represented
as `Nat` values, so if we want to have literals for `ℕ`, we need to convert.
See the `OfNat` instance below for more details.
-/
def fromNat : Nat → ℕ
| 0 => zero
| n+1 => step (fromNat n)

def ofNat {n : Nat} : OfNat ℕ n := {
  ofNat := fromNat n
}

def literals : Literals ℕ := {
  literal := ofNat
  literal_zero := Rel.refl
  literal_step := Rel.refl
}

end literals

section sign

variable [Core ℕ]

def positive_ops : Signed.Positivity.Ops ℕ := {
  Positive := λ n => n ≄ 0
}

def positivity : Signed.Positivity ℕ := {
  positive_defn := Iff.intro id id
}

def sign : Sign ℕ := {
  positivity := positivity
}

end sign

section order

variable [Core ℕ]
variable [Addition ℕ]

local instance le_ex_add : LE ℕ := LE.mk λ n m => ∃ k : ℕ, n + k ≃ m
def lt_le_neqv : LT ℕ := LT.mk λ n m => n ≤ m ∧ n ≄ m

def order : Order ℕ := {
  leOp := le_ex_add
  le_defn := Iff.intro id id

  ltOp := lt_le_neqv
  lt_defn := Iff.intro id id
}

end order

end Lean4Axiomatic.Natural.Impl.Generic
