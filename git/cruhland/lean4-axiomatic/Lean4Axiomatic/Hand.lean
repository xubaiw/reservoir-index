
namespace Lean4Axiomatic

/-! # Handedness -/

/--
Handedness: either left-handed or right-handed.

Intended to be used as a more meaniningful `Bool` type in contexts where it
applies. One example is in selecting the left- or right-hand side of an ordered
pair. Another is in specifying which side of a binary operator an algebraic
property acts on; a common one is the concept of a left inverse (`a⁻¹ * a ≃ 1`)
vs. a right inverse (`a * a⁻¹ ≃ 1`).
-/
inductive Hand where
| /-- Left hand.  -/ L
| /-- Right hand. -/ R

/--
Selects the left-hand or right-hand argument, according to the given `Hand`.

**Named parameters**
- `α`: The `Sort` of the items to select.
-/
abbrev Hand.pick {α : Sort u} : Hand → α → α → α
| L, x, y => x
| R, x, y => y

end Lean4Axiomatic
