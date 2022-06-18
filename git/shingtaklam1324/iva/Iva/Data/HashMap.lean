import Std.Data.HashMap
import Iva.Data.HashSet

namespace Std

namespace HashMap

variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

def keys (m : HashMap α β) : HashSet α :=
  m.fold (init := HashSet.empty) λ s k _ => s.insert k

section BEq

variable [BEq β]

instance : BEq (HashMap α β) where
  beq m₁ m₂ := m₁.toList == m₂.toList

end BEq

end HashMap

end Std
