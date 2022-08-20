import Lean4Axiomatic.Natural.Core

namespace Lean4Axiomatic.Natural.Default

variable {ℕ : Type}
variable [Constructors ℕ]

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

def literals [Equality ℕ] : Literals ℕ := {
  literal := ofNat
  literal_zero := Rel.refl
  literal_step := Rel.refl
}

end Lean4Axiomatic.Natural.Default
