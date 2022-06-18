import Iva.Monomial.ToString
import Iva.Term

variable {α : Type u} [BEq α] [Hashable α] [Fintype α] [ToString α]
variable {R : Type v} [ToString R]

instance : ToString (Term R α) where
  toString t := s!"{t.coeff}⬝{t.monom}"
