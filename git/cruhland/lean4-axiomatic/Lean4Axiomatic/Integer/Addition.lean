
namespace Lean4Axiomatic.Integer

/-!
# Definition and properties of integer addition
-/

/--
Definition of addition, and properties that it must satisfy.

All other properties of addition can be derived from these.
-/
class Addition.Base (ℤ : Type) :=
  /-- Definition of and syntax for addition. -/
  addOp : Add ℤ

namespace Addition
export Addition.Base (addOp)
end Addition

end Lean4Axiomatic.Integer
