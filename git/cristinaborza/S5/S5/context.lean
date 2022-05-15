import S5.language

def ctx := List form 

inductive List.element { α : Type } : List α → α → Prop 
| head (a : α) (l : List α) : element (a :: l) a 
| cons (a b : α) (l : List α) : element l a → element (b :: l) a
 
inductive List.subset { α : Type } : List α → List α → Prop where
| nil (l : List α) : subset [] l 
| cons (a : α) (l₁ l₂: List α) : element l₂ a → subset l₁ l₂ → subset (a :: l₁) l₂

inductive List.equiv { α : Type } : List α → List α → Prop where
| refl (l : List α) : equiv l l
| antisymm (l₁ l₂ : List α) : subset l₁ l₂ → subset l₂ l₁ → equiv l₁ l₂

notation Γ "∪" p => p :: Γ
notation p "∈" Γ => List.element Γ p
notation Δ "⊆" Γ => List.subset Δ Γ
notation Δ "~" Γ => List.equiv Δ Γ  

