/- Semantics -/
import TBA.While.Com

namespace While

open Com

abbrev State (Γ : Ctxt) := (τ : Ty) → (x : VName) → Γ x = some τ → Option (Val τ)

namespace State

def empty : State Γ := λ _ _ _ => none

def update (m : State Γ) (x : VName) (_ : Γ x = some τ) (v : Option (Val τ))
    : State Γ := λ τ' x' h' =>
  if hτ : τ = τ' then (if x = x' then hτ ▸ v else m τ' x' h') else m τ' x' h'

def merge (m₁ : State Γ) (m₂ : State Γ) : State Γ := λ τ x h =>
  if m₁ τ x h = m₂ τ x h then m₁ τ x h else none

-- Update syntax is extended to include proof of the variable's type
scoped notation:max m "[" h " : " x " ↦ " v "]" => update m x h v

end State

namespace Expr

variable (σ : State Γ) in
def eval : Expr Γ τ → Option (Val τ)
  | Expr.const v => v
  | Expr.var x h => σ τ x h
  | Expr.binop e₁ op e₂ =>
    match eval e₁, eval e₂ with
    | some v₁, some v₂ => some (op.eval v₁ v₂)
    | _,       _       => none

def time : Expr Γ τ → Nat
  | Expr.const _ => 1
  | Expr.var _ _ => 1
  | Expr.binop e₁ _ e₂ => time e₁ + time e₂ + 1

end Expr

open Expr
open State

section
set_option hygiene false  -- HACK: allow forward reference in notation
-- note the `local` to make the hacky notation local to the current section
local notation:60 "⟨" c ", " σ "⟩"  " ⇓ " σ' " : " t:60 => Bigstep c σ σ' t

inductive Bigstep : Com Γ → State Γ → State Γ → Nat → Prop where
  | skip :
    ⟨skip, σ⟩ ⇓ σ : 1
  | ass :
    ⟨Com.ass x e h, σ⟩ ⇓ σ[h : x ↦ Expr.eval σ e] : e.time + 1
  | seq (h₁ : ⟨c₁, σ⟩ ⇓ σ' : t₁) (h₂ : ⟨c₂, σ'⟩ ⇓ σ'' : t₂) :
    ⟨c₁;; c₂, σ⟩ ⇓ σ'' : t₁ + t₂ + 1
  | ifTrue (hb : eval σ b = true) (ht : ⟨cₜ, σ⟩ ⇓ σ' : t) :
    ⟨.cond b cₜ cₑ, σ⟩ ⇓ σ' : b.time + t + 1
  | ifFalse (hb : eval σ b = false) (he : ⟨cₑ, σ⟩ ⇓ σ' : t) :
    ⟨.cond b cₜ cₑ, σ⟩ ⇓ σ' : b.time + t + 1
  | whileTrue (hb : eval σ b = true) (hc : ⟨c, σ⟩ ⇓ σ' : t₁) (hind : ⟨.while b c, σ'⟩ ⇓ σ'' : t₂) :
    ⟨.while b c, σ⟩ ⇓ σ'' : b.time + t₁ + t₂ + 1
  | whileFalse (hb : eval σ b = false) :
    ⟨.while b c, σ⟩ ⇓ σ : b.time + 1
end

-- redeclare "proper" notation with working pretty printer
notation:60 "⟨" c ", " σ "⟩"  " ⇓ " σ' " : " t:60 => Bigstep c σ σ' t

end While
