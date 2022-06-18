import Std.Data.HashSet

namespace Std

namespace HashSet

variable {α : Type u} [BEq α] [Hashable α]

def union (s₁ s₂ : HashSet α) : HashSet α :=
  s₁.fold (init := s₂) λ s x => s.insert x

def filter (s : HashSet α) (f : α → Bool) : HashSet α :=
  s.fold (init := HashSet.empty) λ s x => if f x then s.insert x else s

instance : BEq (HashSet α) where
  beq s₁ s₂ := s₁.toList == s₂.toList

end HashSet

end Std
