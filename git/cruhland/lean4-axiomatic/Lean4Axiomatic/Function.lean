
namespace Lean4Axiomatic
namespace Function

/-! # Definitions and properties pertaining to functions -/

/--
This class generalizes the symmetric and commutative properties.

There are some useful results that apply both to symmetric and commutative
operations. Using this class allows the results to be given by a single
definition. See `Lean4Axiomatic.AA.substR_from_substL_swap` for an example.

See `Swappable.swap` for details about the actual property.

**Named parameters**
- `α`: the argument type of the swappable binary operation `f`.
- `β`: the result type of the swappable binary operation `f`.
- `f`: the binary operation whose arguments are "swappable" under `R`.
- `R`: the binary relation that holds between "swapped" invocations of `f`.
-/
class Swappable {α : Sort u} {β : Sort v} (f : α → α → β) (R : β → β → Prop) :=
  /--
  The relation `R` holds between any two invocations of `f` that have the same
  arguments, but provided in the opposite order as each other.

  There are many useful things that obey this property. If `β` is `Prop` and
  `R` is implication (`· → ·`) then `f` is a symmetric relation. If `R` is
  equality or an equivalence relation, then `f` is a commutative function.

  **Named parameters**
  - `x`, `y`: the arguments to `f`.
  -/
  swap : {x y : α} → R (f x y) (f y x)

export Swappable (swap)

/--
If a relation `R` is swappable over one direction of an implication, then it is
automatically swappable over the other direction (and therefore both).

**Intuition**: If `R x y → R y x` for all `x` and `y`, then it must also be
true that `R y x → R x y`, by substituting `y` for `x` and vice versa.

**Named parameters**
- `α`: the type of `R`'s arguments.
- `R`: the swappable binary relation.

**Class parameters**
- `Swappable R (· → ·)`: evidence that `R` is swappable over implication.
-/
instance swappable_over_iff_from_swappable_over_implication
    {α : Sort u} {R : α → α → Prop}
    [inst : Swappable R (· → ·)] : Swappable R (· ↔ ·)
    := {
  swap := Iff.intro (swap (self := inst)) (swap (self := inst))
}

end Function

namespace Fn
export Function (swap Swappable)
end Fn

end Lean4Axiomatic
