import Lean4Axiomatic.Hand

namespace Lean4Axiomatic.AA

/-!
# Core definitions

These are used frequently by other abstract algebra definitions.
-/

/--
Defines a convention for which side of a binary operator its first argument is
sent to.

The given operator, of type `α → α → β`, is assumed to be left-handed; i.e.,
its first argument is on the left when written infix. This function outputs a
modified operator that puts the first argument on whatever side is specified by
the `Hand` argument.

This allows both the left- and right-handed versions of an algebraic property
to share a single definition, avoiding repetitive code. See `AA.DistributiveOn`
for an example.
-/
def forHand {α : Sort u} {β : Sort v} : Hand → (α → α → β) → (α → α → β)
| Hand.L => id
| Hand.R => flip

/--
The predicate that is always true.

The name `tc` is short for "trivial constraint", because the intended use of
this definition is to fill in constraint arguments of abstract algebra
typeclasses when they're not needed. It's important that the name is as short
as possible, to reduce clutter. See usages of `Substitutive₂` for examples.
-/
abbrev tc {α : Sort u} : α → Prop := λ _ => True

end Lean4Axiomatic.AA
