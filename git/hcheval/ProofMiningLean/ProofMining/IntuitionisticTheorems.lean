-- Chapter 9.3 From "Articol metateoreme"

import ProofMining.Proof
import ProofMining.Formula
import ProofMining.IntuitionisticRules

open Formula (falsum WellFormed)
namespace Proof

set_option maxHeartbeats 1000000

theorem t19 (A B : Formula) 
  (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) :
  e ;; Γ ⊢ (A ⋀ B ⟹ B) := 
  let p₁ : e ;; Γ ⊢ (A ⋀ B ⟹ B ⋀ A) := permConj
  let p₂ : e ;; Γ ⊢ (B ⋀ A ⟹ B) := weakConj
  syllogism p₁ p₂

theorem t20 (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : e ;; Γ ⊢ (B ⟹ A ⋁ B) := 
  let p₁ : e ;; Γ ⊢ (B ⟹ B ⋁ A) := weakDisj 
  let p₂ : e ;; Γ ⊢ (B ⋁ A ⟹ A ⋁ B) := permDisj 
  syllogism p₁ p₂

theorem t21 (A : Formula) (_ : WellFormed e A := by autowf) : e ;; Γ ⊢ A ⟹ A :=
  let p₁ : e ;; Γ ⊢ A ⟹ A ⋀ A := contrConj 
  let p₂ : e ;; Γ ⊢ A ⋀ A ⟹ A := weakConj 
  syllogism p₁ p₂

theorem t18 (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : e ;; Γ ⊢ (∼A ⋀ A ⟹ B) :=
  let p₁ : e ;; Γ ⊢ (falsum ⟹ B) := exFalso
  let p₂ : e ;; Γ ⊢ ∼(∼A ⋀ A) := importation (t21 ∼A)
  syllogism p₂ p₁

theorem t22 (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  e ;; Γ ⊢ A ⟹ (B ⟹ (A ⋀ B)) :=
  let p₁ : e ;; Γ ⊢ (A ⋀ B) ⟹ (A ⋀ B) := t21 _
  exportation p₁

theorem t23 (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  e ;; Γ ⊢ A ⟹ (B ⟹ A) :=
  let p₁ : e ;; Γ ⊢ (A ⋀ B) ⟹ A := weakConj
  exportation p₁ 

theorem t24 (A : Formula) (_ : WellFormed e A := by autowf) : 
  e ;; Γ ⊢ (A ⟹ ∼∼A) :=
  let p₁ : e ;; Γ ⊢ (A ⋀ ∼A ⟹ ∼A ⋀ A) := permConj 
  let p₂ : e ;; Γ ⊢ ∼(A ⋀ ∼A) := syllogism p₁ (t18 A falsum)
  exportation p₂

theorem t26a (A : Formula) (_ : WellFormed e A := by autowf) : 
  e ;; Γ ⊢ ∼A ⟹ ∼∼∼A :=
  t24 ∼A

theorem t26b (A : Formula) (_ : WellFormed e A := by autowf) : 
  e ;; Γ ⊢ ∼∼∼A ⟹ ∼A :=
  let p₁ : e ;; Γ ⊢ A ⟹ ∼∼∼∼A := syllogism (t24 _) (t24 _)
  let p₂ : e ;; Γ ⊢ ∼∼∼A ⋀ A ⟹ falsum := syllogism (permConj) (importation p₁)
  exportation p₂

theorem t28a (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  e ;; Γ ⊢ ∼∼(A ⟹ B) ⟹ (∼∼A ⟹ ∼∼B) :=
  sorry

theorem t28b (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  e ;; Γ ⊢ (∼∼A ⟹ ∼∼B) ⟹ ∼∼(A ⟹ B) :=
  let p₁ : e ;; Γ ⊢ (A ⟹ B) ⟹ ∼∼A ⟹ (A ⟹ B) := t23 _ _
  let p₂ : e ;; Γ ⊢ (A ⟹ B) ⋀ ∼∼A ⋀ A ⟹ ∼∼B := syllogism (importation (importation p₁)) (t24 B)
  let p₃ : e ;; Γ ⊢ (A ⟹ B) ⋀ ∼∼A ⟹ (A ⟹ B) ⋀ ∼∼A ⋀ A := sorry
  let p₄ : e ;; Γ ⊢ (A ⟹ B) ⋀ ∼∼A ⟹ ∼∼B := syllogism p₃ p₂
  -- let p₅ (h₁: Γ ⊢ A ⟹ B) : Γ ⊢ ∼A ⟹ ∼B := sorry
  let p₆ : e ;; Γ ⊢ (A ⟹ B) ⟹ (∼∼A ⟹ ∼∼B) := exportation p₄
  let p₇ : e ;; Γ ⊢ ∼(A ⟹ B) ⟹ ∼(∼∼A ⟹ ∼∼B) := sorry
  sorry

theorem t27a (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  e ;; Γ ⊢ ∼∼(A ⟹ B) ⟹ (A ⟹ ∼∼B) :=
  let p₀ : e ;; Γ ⊢ (∼∼(A ⟹ B)) ⋀ ∼∼A ⟹ ∼∼B := importation (t28a _ _)
  let p₁ : e ;; Γ ⊢ ∼∼A ⋀ (∼∼(A ⟹ B)) ⟹ (∼∼(A ⟹ B)) ⋀ ∼∼A := permConj
  let p₂ : e ;; Γ ⊢ ∼∼A ⋀ (∼∼(A ⟹ B)) ⟹ ∼∼B := syllogism p₁ p₀
  let p₃ : e ;; Γ ⊢ ∼∼A ⟹ ∼∼(A ⟹ B) ⟹ ∼∼B := exportation p₂
  let p₄ : e ;; Γ ⊢ A ⟹ ∼∼(A ⟹ B) ⟹ ∼∼B := syllogism (t24 _) p₃
  exportation (syllogism (permConj) (importation p₄))

-- theorem t27b (A B : Formula) : Γ ⊢ (A ⟹ ∼∼B) ⟹ ∼∼(A ⟹ B) :=
--   sorry

theorem t29a (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  e ;; Γ ⊢ (A ⟹ ∼B) ⟹ (∼∼A ⟹ ∼B) :=
  let p₁ : e ;; Γ ⊢ (A ⟹ ∼B) ⟹ (∼∼A ⟹ ∼∼∼B) := syllogism (t24 _) (t28a _ _)
  let p₂ : e ;; Γ ⊢ (∼∼A ⟹ ∼∼∼B) ⟹ (∼∼A ⟹ ∼B) := exportation (syllogism (importation (t21 _)) (t26b _))
  syllogism p₁ p₂

-- theorem t29b (A B : Formula) : Γ ⊢ (∼∼A ⟹ ∼B) ⟹ (A ⟹ ∼B) :=
--   sorry

-- theorem t30a (A B : Formula) : Γ ⊢ ∼∼(A ⋀ B) ⟹ (∼∼A ⋀ ∼∼B) :=
--   sorry

-- theorem t30b (A B : Formula) : Γ ⊢ (∼∼A ⋀ ∼∼B) ⟹ ∼∼(A ⋀ B) :=
--   sorry

-- theorem t31 (A B : Formula) : Γ ⊢ ∼∼(A ⋁ B) ⟹ ∼∼A ⟹ ∼∼B :=
--   sorry

-- theorem t32a (A B : Formula) : Γ ⊢ ∼∼(A ⋁ B) ⟹ ∼∼(∼A ⋀ ∼B) :=
--   sorry

theorem t32b (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  e ;; Γ ⊢ ∼(∼A ⋀ ∼B) ⟹ ∼∼(A ⋁ B) :=
  sorry

theorem t25 (A : Formula) (_ : WellFormed e A := by autowf) : 
  e ;; Γ ⊢ ∼∼(A ⋁ ∼A) := 
  let p₁ : e ;; Γ ⊢ ∼(∼A ⋀ ∼∼A) := syllogism (permConj) (t18 _ _)
  mpon p₁ (t32b _ _)

theorem t33a (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  e ;; Γ ⊢ ∼(A ⋀ B) ⟹ A ⟹ ∼B :=
  let p₁ : e ;; Γ ⊢ ∼(A ⋀ B) ⋀ (A ⋀ B) ⟹ falsum := t18 _ _
  let p₂ : e ;; Γ ⊢ (B ⟹ ∼∼(A ⋀ B)) ⟹ ∼(A ⋀ B) ⟹ ∼B := sorry
  sorry

theorem t33b (A B : Formula) : e ;; Γ ⊢ (A ⟹ ∼B) ⟹ ∼(A ⋀ B) :=
  sorry

theorem t35 (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) :
  e ;; Γ ⊢ A ⋁ B ⟹ ∼A ⟹ B :=
  let p₁ : e ;; Γ ⊢ ∼A ⋀ A ⟹ B := t18 _ _
  let p₂ : e ;; Γ ⊢ A ⟹ ∼A ⟹ B := exportation (syllogism (permConj) p₁)
  let p₃ : e ;; Γ ⊢ B ⟹ ∼A ⟹ B := t23 _ _
  r49 p₂ p₃

theorem t40a (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  e ;; Γ ⊢ ∼(A ⋁ B) ⟹ (∼A ⋀ ∼B) :=
  let p₃ : e ;; Γ ⊢ A ⟹ ∼∼ (A ⋁ B) := syllogism (weakDisj) (t24 (A ⋁ B))
  let p₄ : e ;; Γ ⊢ ∼(A ⋁ B) ⋀ A ⟹ falsum := syllogism (permConj) (importation p₃)
  let p₁ : e ;; Γ ⊢ ∼(A ⋁ B) ⟹ ∼A := exportation p₄
  let p₅ : e ;; Γ ⊢ B ⟹ ∼∼ (A ⋁ B) := syllogism (t20 A B) (t24 (A ⋁ B))
  let p₆ : e ;; Γ ⊢ ∼(A ⋁ B) ⋀ B ⟹ falsum := syllogism (permConj) (importation p₅)
  let p₂ : e ;; Γ ⊢ ∼(A ⋁ B) ⟹ ∼B := exportation p₆
  r45 p₁ p₂

theorem t40b (A B : Formula) (_ : WellFormed e A := by autowf) (_ : WellFormed e B := by autowf) : 
  e ;; Γ ⊢ (∼A ⋀ ∼B) ⟹ ∼(A ⋁ B) :=
  let p₁ : e ;; Γ ⊢ A ⟹ ∼A ⟹ ∼∼B := exportation (syllogism (permConj) (t18 _ _))
  let p₂ : e ;; Γ ⊢ B ⟹ ∼A ⟹ ∼∼B := exportation (syllogism (permConj) (importation (r44 (t24 _))))
  let p₃ : e ;; Γ ⊢ A ⋁ B ⟹ ∼A ⟹ ∼∼B := r49 p₁ p₂
  let p₄ : e ;; Γ ⊢ (∼A ⟹ ∼∼B) ⟹ ∼(∼A ⋀ ∼B) := t33b _ _
  let p₅ : e ;; Γ ⊢ A ⋁ B ⟹ ∼(∼A ⋀ ∼B) := syllogism p₃ p₄
  exportation (syllogism (permConj) (importation p₅))