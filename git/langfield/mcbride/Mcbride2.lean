import Mcbride

universe u

def mapPair {α α' β β' : Type u} (f : α → α') (g : β → β') : Product α β → Product α' β'
| ⟨a, b⟩ => ⟨f a, g b⟩

def mapEither {α α' β β' : Type u} (f : α → α') (g : β → β') : Either α β → Either α' β'
| Either.inl a => Either.inl <| f a
| Either.inr b => Either.inr <| g b

-- 'K' for 'KONSTANT' (in German).
def combinatorK {α ε : Type u} : α → (ε → α) := λ a e => a

def combinatorS {α b γ : Type u} : (γ → α → β) → (γ → α) → γ → β :=
  λ abc ca c => abc c (ca c)

-- `λ x => x` is the easy way; let's do it a funny way to make a point.
def identity {χ : Type u} : χ → χ :=
  combinatorS combinatorK (@combinatorK χ Zero)
