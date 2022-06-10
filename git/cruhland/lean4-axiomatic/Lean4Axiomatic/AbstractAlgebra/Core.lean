import Lean4Axiomatic.Hand

namespace Lean4Axiomatic

/-!
# Core definitions

These are used frequently by other abstract algebra definitions.
-/

/--
Performs "alignment" of a heterogeneous binary operator.

By convention, binary operators are considered to be left-handed by default; in
other words, their first arguments are always on the left when written infix.
Right-hand alignment swaps the arguments, so that the first argument is given
on the right with infix notation.

This function outputs an operator that is equivalent to the one it receives as
input, except that it will be aligned according to the `Hand` parameter. The
input operator is assumed to be left-handed.

This allows both the left- and right-handed versions of an algebraic property
to share a single definition, avoiding repetitive code. See `AA.DistributiveOn`
for an example.

**Named parameters**
- `α`: The `Sort` of the operator's first (default left) parameter.
- `β`: The `Sort` of the operator's second (default right) parameter.
- `γ`: The `Sort` of the operator's result.

**Return type**: The return type contains what should be considered inputs to
this function, but they are to the right of the colon so that they can be
referenced in pattern matching. The first parameter is the `Hand` to use for
alignment, and the second parameter is the operator to align. The rest of the
return type denotes the output: the aligned version of the operator.
-/
abbrev Hand.hAlign
    {α β : Sort u} {γ : Sort v}
    : (hand : Hand) → (α → β → γ) → (hand.pick α β → hand.pick β α → γ)
| Hand.L => id
| Hand.R => flip

/--
Performs "alignment" of a homogeneous binary operator.

This is a specialization of `Hand.hAlign` to operators whose left and right
parameters have the same type (i.e., homogeneous operators). This is much more
common than the heterogeneous case, so this definition exists for convenience.

See `Hand.hAlign` for more details on the purpose of this function.

**Named parameters**
- `α`: The `Sort` of the operator's input parameters.
- `β`: The `Sort` of the operator's result.

**Return type**: The return type contains what should be considered inputs to
this function, but they are to the right of the colon so that they can be
referenced in pattern matching. The first parameter is the `Hand` to use for
alignment, and the second parameter is the operator to align. The rest of the
return type denotes the output: the aligned version of the operator.
-/
abbrev Hand.align {α : Sort u} {β : Sort v} : Hand → (α → α → β) → (α → α → β)
| Hand.L => Hand.L.hAlign
| Hand.R => Hand.R.hAlign

/--
The predicate that is always true.

The name `tc` is short for "trivial constraint", because the intended use of
this definition is to fill in constraint arguments of abstract algebra
typeclasses when they're not needed. It's important that the name is as short
as possible, to reduce clutter. See usages of `Substitutive₂` for examples.
-/
abbrev AA.tc {α : Sort u} : α → Prop := λ _ => True

end Lean4Axiomatic
