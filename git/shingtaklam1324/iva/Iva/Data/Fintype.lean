class Fintype (α : Type u) :=
(univ : List α)
(is_univ : ∀ x, x ∈ univ)

namespace List

variable {α : Type u} [Fintype α]

def univ : List α := Fintype.univ

end List
