import ProofMining.Formula
import ProofMining.Util 
import ProofMining.Automation

open Formula (falsum WellFormed highereq)
open Term (WellTyped)



inductive Proof : Environment → List Formula →  Formula →  Type
| contrConj {e : Environment} {Γ : List Formula} {A : Formula} (_ : WellFormed e A := by autowf) : 
  Proof e Γ (A ⟹ A ⋀ A)
| contrDisj {e : Environment} {Γ : List Formula} {A : Formula} (_ : WellFormed e A := by autowf) :
  Proof e Γ (A ⋁ A ⟹ A)
| weakConj {e : Environment} {Γ : List Formula} {A B : Formula} (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  Proof e Γ (A ⋀ B ⟹ A)
| weakDisj {e : Environment} {Γ : List Formula} {A B : Formula} (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  Proof e Γ (A ⟹ A ⋁ B)
| permConj {e : Environment} {Γ : List Formula} {A B : Formula} (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  Proof e Γ (A ⋀ B ⟹ B ⋀ A)
| permDisj {e : Environment} {Γ : List Formula} {A B : Formula} (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  Proof e Γ (A ⋁ B ⟹ B ⋁ A)
| exFalso {e : Environment} {Γ : List Formula} {A : Formula} (_ : WellFormed e A := by autowf) : 
  Proof e Γ (falsum ⟹ A)
| universalAxiom {e : Environment} {Γ : List Formula} {ρ : FiniteType} {A : Formula} (t : Term) 
  (_ : WellFormed (ρ :: e) A := by autowf) (_ : WellTyped e t ρ) :
  Proof e Γ (∀∀ ρ A ⟹ Formula.subst A 0 t)
| existentialAxiom {ρ : FiniteType} {A : Formula} (t : Term) (_ : WellFormed (ρ :: e) A) (_ : WellTyped e t ρ) : 
  Proof e Γ (Formula.subst A 0 t ⟹ ∃∃ ρ A)
| mpon {e : Environment} {Γ : List Formula} {A B : Formula} : 
  Proof e Γ A → Proof e Γ (A ⟹ B) → (_ : WellFormed e A := by autowf) → (_ : WellFormed e B := by autowf) → Proof e Γ B
| syllogism {e : Environment} {Γ : List Formula} {A B C : Formula} : 
  Proof e Γ (A ⟹ B) → Proof e Γ (B ⟹ C) → 
  (_ : WellFormed e A := by autowf) → (_ : WellFormed e B := by autowf) → (_ : WellFormed e C := by autowf) → 
  Proof e Γ (A ⟹ C)
| exportation {e : Environment} {Γ : List Formula} {A B C : Formula} :
  Proof e Γ (A ⋀ B ⟹ C) → (_ : WellFormed e A := by autowf) → (_ : WellFormed e B := by autowf) → (_ : WellFormed e C := by autowf) → 
  Proof e Γ (A ⟹ B ⟹ C)
| importation {e : Environment} {Γ : List Formula}{A B C : Formula} : 
  Proof e Γ (A ⟹ B ⟹ C) → 
  (_ : WellFormed e A := by autowf) → (_ : WellFormed e B := by autowf) → (_ : WellFormed e C := by autowf) → 
  Proof e Γ (A ⋀ B ⟹ C)
| expansion {e : Environment} {Γ : List Formula}{A B : Formula} (C : Formula) : 
  Proof e Γ (A ⟹ B) → 
  (_ : WellFormed e A := by autowf) → (_ : WellFormed e B := by autowf) → (_ : WellFormed e C := by autowf) →
  Proof e Γ (C ⋁ A ⟹ C ⋁ B)
| universalRule {e : Environment} {Γ : List Formula}{A B : Formula} {ρ : FiniteType} (_ : WellFormed (ρ :: e) A := by autowf) (_ : WellFormed e B := by autowf): 
  Proof e Γ (B ⟹ A) →  Proof e Γ (B ⟹ ∀∀ ρ A) 
| existentialRule {e : Environment} {Γ : List Formula}{A B : Formula} {ρ : FiniteType} (_ : WellFormed (ρ :: e) A := by autowf) (_ : WellFormed e B := by autowf) : 
  Proof e Γ (A ⟹ B) →  Proof e Γ (∃∃ ρ A ⟹ B)
| premise {e : Environment} {Γ : List Formula} {A : Formula} : 
  (∀ P, P ∈ Γ → WellFormed e P) → A ∈ Γ → Proof e Γ A


namespace Proof

section 
  variable {Γ : List Formula} {A B C : Formula}



end

namespace Proof

notation env ";;" Γ " ⊢ " A => Proof env Γ A


