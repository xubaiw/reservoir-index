import Iva.Monomial
import Iva.Data.Fintype

/-
Note that all of the orderings in this file return true if `m₁ ≤ m₂` inder the
given ordering.

Furthermore, even though we do not require that `α` has `LE`, we implicitly
assume that `α` has a linear order, and the result of `List.univ` is `α` in
*increasing* order.
-/

namespace Monomial

namespace Ordering

variable (α : Type u) [BEq α] [Hashable α] [Fintype α]

private def lexAux (m₁ m₂ : Monomial α) : List α → Bool
| [] => True
| a :: as => (m₁.exponent a ≤ m₂.exponent a) &&
             (m₁.exponent a != m₂.exponent a || lexAux m₁ m₂ as)

def lex (m₁ m₂ : Monomial α) : Bool := lexAux α m₁ m₂ List.univ

def revLex (m₁ m₂ : Monomial α) : Bool := lexAux α m₁ m₂ List.univ.reverse

def grLex (m₁ m₂ : Monomial α) : Bool := m₁.degree ≤ m₂.degree &&
  (m₁.degree != m₂.degree || lex α m₁ m₂)

def gRevLex (m₁ m₂ : Monomial α) : Bool := m₁.degree ≤ m₂.degree &&
  (m₁.degree != m₂.degree || revLex α m₁ m₂)

end Ordering

end Monomial
