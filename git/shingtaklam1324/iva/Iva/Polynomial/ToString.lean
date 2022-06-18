import Iva.Term.ToString
import Iva.Polynomial

variable {α : Type u} [BEq α] [Hashable α] [Fintype α] [ToString α]
variable {R : Type v} [ToString R] [BEq R]

instance : ToString (Polynomial R α) where
  toString p :=
    if p.terms == [] then
      "0"
    else
      " + ".intercalate <| p.terms.map toString
