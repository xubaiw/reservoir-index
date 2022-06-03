/-!
# Operator syntax

Defines classes and syntax for mathematical operators. The goal is to make the
operators general enough to be useful but specific enough to be understandable.
-/

namespace Operators

/--
Provides the `· ≃ ·` operator.

Intended to be used for equality or equivalence relations.

**Named parameters**
- `α`: the `Sort` of the operator's arguments.
-/
class TildeDash (α : Sort u) :=
  /-- The `· ≃ ·` operator. -/
  tildeDash : α → α → Prop

export TildeDash (tildeDash)

infix:50 " ≃ " => tildeDash

/--
The `· ≄ ·` operator, the negation of `TildeDash.tildeDash`.

**Named parameters**
- `α`: the `Sort` of the operator's arguments.
- `x`: the left argument of the operator.
- `y`: the right argument of the operator.

**Class parameters**
- `TildeDash α`: provides the operation that is being negated.
-/
abbrev tildeDashNot {α : Sort u} [TildeDash α] (x y : α) : Prop :=
  ¬ (x ≃ y)

infix:50 " ≄ " => tildeDashNot

/--
Provides the `· ≃? ·` operator.

Explicitly defined to be a decision prodcedure, for a relation intended to be
equality or equivalence.

**Named parameters**
- `α`: the `Sort` of the operator's arguments.
- `β`: the decidable relation.
-/
class TildeDashQuestion {α : Sort u} (β : α → α → Prop) :=
  /--
  The `· ≃? ·` operator, a decision procedure for `β`.

  See `TildeDashQuestion` for documentation on the class-level parameters.
  -/
  tildeDashQuestion : DecidableRel β

export TildeDashQuestion (tildeDashQuestion)

attribute [instance] tildeDashQuestion

infix:50 " ≃? " => tildeDashQuestion

/--
The `· ≮ ·` operator, the negation of `LT.lt`.

**Named parameters**
- `α`: the `Type` of the operator's arguments.
- `x`: the left argument of the operator.
- `y`: the right argument of the operator.

**Class parameters**
- `LT α`: provides the operation that is being negated.
-/
def ltNot {α : Type u} [LT α] (x y : α) : Prop := ¬ (x < y)

infix:50 " ≮ " => ltNot

end Operators
