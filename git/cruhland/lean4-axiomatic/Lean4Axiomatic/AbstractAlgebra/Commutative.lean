import Lean4Axiomatic.Relation.Equivalence

namespace Lean4Axiomatic.AA

open Relation.Equivalence (EqvOp)

/--
Class for types and operations that satisfy the commutative property.

For more information see `Commutative.comm` or
[consult Wikipedia](https://en.wikipedia.org/wiki/Commutative_property).

**Named parameters**
- `α`: the type of the arguments to the binary operation `f`.
- `β`: the result type of the binary operation `f`.
- `f`: the binary operation that obeys the commutative property.

**Class parameters**
- `EqvOp β`: necessary because the property expresses an equality on `β`.
-/
class Commutative {α : Sort u} {β : Sort v} [EqvOp β] (f : α → α → β) where
  /--
  The commutative property of a binary operation `f`.

  Some well-known examples from arithmetic are that addition and multiplication
  are commutative; we have `a + b ≃ b + a` and `a * b ≃ b * a` for all natural
  numbers `a` and `b`.

  **Named parameters**
  - see `Commutative` for the class parameters.
  - `x` and `y`: the operands of `f`.
  -/
  comm {x y : α} : f x y ≃ f y x

export Commutative (comm)

end Lean4Axiomatic.AA
