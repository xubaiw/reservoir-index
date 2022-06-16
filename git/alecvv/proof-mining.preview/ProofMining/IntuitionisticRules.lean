-- Chapter 9.4 From "Articol rules"

import ProofMining.Proof
import ProofMining.Formula

open Formula (falsum WellFormed)
namespace Proof

 
variable {A B C : Formula} {e : Environment} {Γ : List Formula} 

theorem r44 
  (hyp : (e ;; Γ ⊢ A)) 
  (wfA : WellFormed e A := by autowf) (wfB : WellFormed e B := by autowf)
  : e ;; Γ ⊢ B ⟹ A :=
  let p₁ : e ;; Γ ⊢ A ⋀ B ⟹ A := weakConj (by assumption) (by assumption)
  let p₂ : e ;; Γ ⊢ A ⟹ (B ⟹ A) := exportation p₁ (by assumption) (by assumption) (by assumption)
  mpon hyp p₂ (by assumption) (by constructor <;> assumption)


set_option maxHeartbeats 1000000

theorem r45 (h₁ : e ;; Γ ⊢ A ⟹ B) (h₂ : e ;; Γ ⊢ A ⟹ C) 
  (wfA : WellFormed e A := by autowf) (wfB : WellFormed e B := by autowf) (wfC : WellFormed e C := by autowf)
  : e ;; Γ ⊢ A ⟹ B ⋀ C :=
  let p₁ : e ;; Γ ⊢ B ⋀ C ⟹ B ⋀ C := syllogism permConj permConj
  let p₂ : e ;; Γ ⊢ B ⟹ (C ⟹ B ⋀ C) := exportation p₁
  let p₃ : e ;; Γ ⊢ A ⟹ (C ⟹ B ⋀ C) := syllogism h₁ p₂ 
  let p₄ : e ;; Γ ⊢ A ⋀ C ⟹ B ⋀ C := importation p₃
  let p₅ : e ;; Γ ⊢ C ⋀ A ⟹ B ⋀ C := syllogism (permConj) p₄
  let p₆ : e ;; Γ ⊢ C ⟹ (A ⟹ B ⋀ C) := exportation p₅
  let p₇ : e ;; Γ ⊢ A ⋀ A ⟹ B ⋀ C := importation (syllogism h₂ p₆)
  syllogism (contrConj) p₇
#check @r44

theorem r46 {A B C : Formula} (h : e ;; Γ ⊢ A ⟹ B) 
  (wfA : WellFormed e A := by autowf) (wfB : WellFormed e B := by autowf) (wfC : WellFormed e C := by autowf)
  : e ;; Γ ⊢ A ⋀ C ⟹ B ⋀ C :=
  let p₁ : e ;; Γ ⊢ C ⋀ A ⟹ B := importation (r44 (h)) 
  let p₂ : e ;; Γ ⊢ A ⋀ C ⟹ B := syllogism (permConj) p₁ 
  let p₃ : e ;; Γ ⊢ A ⋀ C ⟹ C := syllogism (permConj) (weakConj) 
  r45 p₂ p₃


theorem r49 {A B C : Formula} (h₁ : e ;; Γ ⊢ A ⟹ C) (h₂ : e ;; Γ ⊢ B ⟹ C) 
  (wfA : WellFormed e A := by autowf) (wfB : WellFormed e B := by autowf) (wfC : WellFormed e C := by autowf)
  : e ;; Γ ⊢ A ⋁ B ⟹ C :=
  let p₁ : e ;; Γ ⊢ A ⋁ B ⟹ A ⋁ C := expansion A h₂
  let p₂ : e ;; Γ ⊢ C ⋁ A ⟹ C ⋁ C := expansion C h₁
  let p₃ : e ;; Γ ⊢ A ⋁ C ⟹ C ⋁ C := syllogism (permDisj) p₂
  let p₄ : e ;; Γ ⊢ A ⋁ C ⟹ C := syllogism p₃ (contrDisj)
  syllogism p₁ p₄

theorem r50 {A B : Formula} (h₁ : e ;; Γ ⊢ A) (h₂ : e ;; Γ ⊢ B) 
  (wfA : WellFormed e A := by autowf) 
  (wfB : WellFormed e B := by autowf) 
  : e ;; Γ ⊢ A ⋀ B :=
  let p₁ : e ;; Γ ⊢ A ⟹ (B ⟹ A ⋀ B) := exportation (syllogism (permConj) (permConj))
  let p₂ : e ;; Γ ⊢ B ⟹ A ⋀ B  := mpon h₁ p₁
  mpon h₂ p₂

theorem r42 {A : Formula} {ρ : FiniteType} (h₁ : (ρ :: e) ;; Γ ⊢ A) 
  (wfA : WellFormed (ρ :: e) A)
  : e ;; Γ ⊢ ∀∀ ρ A := 
  let p₁ : (ρ :: e) ;; Γ ⊢ A ⟹ A := syllogism (contrConj _) (weakConj _ _) _ _ _
  let p₂ : (ρ :: e) ;; Γ ⊢ A ⟹ ∀∀ ρ A := universalRule p₁
  mpon h₁ p₂

theorem r47 {A : Formula} {ρ : FiniteType} {t : Term} (h₁ : Γ ⊢ ∀∀ ρ A) : Γ ⊢ Formula.subst A 0 t :=
  mpon h₁ (universalAxiom ρ A t)