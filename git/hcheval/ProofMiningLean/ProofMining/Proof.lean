import ProofMining.Formula
import ProofMining.Util 
import ProofMining.Automation

open Formula (falsum WellFormed highereq)
open Term (WellTyped)

/-
  The type of propositional proofs. 
  `Proof Γ A` is to be read as the type of proofs of the formula A from the premises Γ.
  Each constructor correspons to an axiom or a rule of inference.
  We will add more constructors to `Proof` as we extend the system beyond propositional logic.

  Note the presence of the additional constructor `premise` saying that a formula can always be trivially proved when it is taken as a premise.
-/


-- inductive Proof (Γ : List Formula) : Formula →  Type
-- | contrConj {A : Formula} : Proof Γ (A ⟹ A ⋀ A)
-- | contrDisj (A : Formula) : Proof Γ (A ⋁ A ⟹ A)
-- | weakConj (A B : Formula) : Proof Γ (A ⋀ B ⟹ A)
-- | weakDisj (A B : Formula) : Proof Γ (A ⟹ A ⋁ B)
-- | permConj (A B : Formula) : Proof Γ (A ⋀ B ⟹ B ⋀ A)
-- | permDisj (A B : Formula) : Proof Γ (A ⋁ B ⟹ B ⋁ A)
-- | exFalso (A : Formula) : Proof Γ (falsum ⟹ A)
-- | universalAxiom (ρ : FiniteType) (A : Formula) (t : Term) : Proof Γ (∀∀ ρ A ⟹ Formula.subst A 0 t)
-- | existentialAxiom (ρ : FiniteType) (A : Formula) (t : Term) : Proof Γ (Formula.subst A 0 t ⟹ ∃∃ ρ A)
-- | mpon {A B : Formula} : Proof Γ A → Proof Γ (A ⟹ B) → Proof Γ B
-- | syllogism {A B C : Formula} : Proof Γ (A ⟹ B) → Proof Γ (B ⟹ C) → Proof Γ (A ⟹ C)
-- | exportation {A B C : Formula} : Proof Γ (A ⋀ B ⟹ C) → Proof Γ (A ⟹ B ⟹ C)
-- | importation {A B C : Formula} : Proof Γ (A ⟹ B ⟹ C) → Proof Γ (A ⋀ B ⟹ C)
-- | expansion {A B : Formula} (C : Formula) : Proof Γ (A ⟹ B) → Proof Γ (C ⋁ A ⟹ C ⋁ B)
-- | universalRule {A B : Formula} (ρ : FiniteType) : Proof Γ (B ⟹ A) →  Proof Γ (B ⟹ ∀∀ ρ A)
-- | existentialRule {A B : Formula} (ρ : FiniteType) : Proof Γ (A ⟹ B) →  Proof Γ (∃∃ ρ A ⟹ B)
-- | premise {A : Formula} : A ∈ Γ → Proof Γ A
-- | eqZeroRefl (x : Term) : Proof Γ (x ≅ x)
-- | eqZeroSymm (x y : Term) : Proof Γ $ (x ≅ y) ⟹ (y ≅ x)
-- | ezZeroTrans (x y z : Term) : Proof Γ $ (x ≅ y) ⟹ (y ≅ z) ⟹ (x ≅ z)
-- -- | kcombAxiom (ρ τ : FiniteType) (x y : Term) : Proof Γ (highereq ρ (Term.app (Term.app (Term.kcomb ρ τ) x) y) (x))
-- | kcombAxiom (ρ τ : FiniteType) (x y : Term) : Proof Γ (highereq ρ (Term.kcomb ρ τ # x # y) (x))
-- | scombAxiom (δ ρ τ : FiniteType) (x y z : Term) : Proof Γ (highereq τ (Term.app (Term.app (Term.app (Term.scomb δ ρ τ) x) y) z) (Term.app (Term.app x z) (Term.app y z)))
-- | induct {A : Formula} : Proof Γ $ ((A.subst 0 Term.zero) ⋀ (∀∀ FiniteType.zero ((A.subst 0 (Term.var 0)) ⟹ (A.subst 0 (Term.subst Term.successor 0 $ Term.var 0))))) ⟹ (∀∀ FiniteType.zero A)
-- | succAxiomZero (x : Term) : Proof Γ ∼((Term.app Term.successor x) ≅ Term.zero)
-- | succAxiom (x y : Term) : Proof Γ $ ((Term.app Term.successor x) ≅ (Term.app Term.successor y)) ⟹ (x ≅ y)
-- | qfer {A₀ : Formula} {s p r : Term} {ρ τ : FiniteType} : Proof Γ (A₀ ⟹ (highereq ρ s t)) → Proof Γ (A₀ ⟹ highereq τ (Term.subst r 0 s) (Term.subst r 0 p)) 


/-
  This is likely the complete definition of `Proof` in our representation of formulas.
  Just left here for the time being.
-/



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

  /-
    Duplicates of the constructors of `Proof`, but with all arguments implicit.
    In many cases, Lean will be able to infer the arguments of the constructors of `Proof`
    so we might as well avoid having to write them.
    TODO: Decide which is better.
  -/
  -- def contrConj' := @contrConj Γ A
  -- def contrDisj' := @contrDisj Γ A
  -- def weakConj' := @weakConj Γ A B 
  -- def weakDisj' := @weakDisj Γ A B
  -- def permConj' := @permConj Γ A B 
  -- def permDisj' := @permDisj Γ A B
  -- def exFalso' := @exFalso Γ A 
  -- def expansion' := @expansion Γ A B C

end

namespace Proof
/-
  Γ ⊢ A as a notation for Proof Γ A 
-/
notation env ";;" Γ " ⊢ " A => Proof env Γ A





-- section DemoExamples

-- variable (e : Environment) (A B : Formula) (Γ : List Formula) (wfA : WellFormed e A) (wfB : WellFormed e B)

-- /-
--   ### Example 1: The propositional theorem "A implies A"
--     All the proofs are the same, only written in different levels of detail or with different notations,
--     for exemplification purposes only.
-- -/

--   example : Proof Γ (A ⟹ A) :=
--     let p₁ : Proof Γ (A ⟹ A ⋀ A) := contrConj A 
--     let p₂ : Proof Γ (A ⋀ A ⟹ A) := weakConj A A 
--     syllogism p₁ p₂

--   example : Proof Γ (A ⟹ A) :=
--     let p₁ : Proof Γ (A ⟹ A ⋀ A) := contrConj _ 
--     let p₂ : Proof Γ (A ⋀ A ⟹ A) := weakConj _ _ 
--     syllogism p₁ p₂

--   example : Proof Γ (A ⟹ A) := 
--     let p₁ : Proof Γ (A ⟹ A ⋀ A) := contrConj'
--     let p₂ : Proof Γ (A ⋀ A ⟹ A) := weakConj' 
--     syllogism p₁ p₂

--   example : Γ ⊢ A ⟹ A :=
--     let p₁ : Γ ⊢ A ⟹ A ⋀ A := contrConj _ 
--     let p₂ : Γ ⊢ A ⋀ A ⟹ A := weakConj _ _
--     syllogism p₁ p₂

--   example : Proof Γ (A ⟹ A) := syllogism (contrConj _) (weakConj _ _)

-- /-
--   ### Example 2: The propositional rule "from A, one can deduce that B implies A"
--   Written first in detail, then concisely
-- -/

-- example (h : Γ ⊢ A) : Γ ⊢ B ⟹ A :=
--   let p₁ : Γ ⊢ A ⋀ B ⟹ A := weakConj' 
--   let p₂ : Γ ⊢ A ⟹ (B ⟹ A) := exportation p₁ 
--   mpon h p₂

-- example (h : Γ ⊢ A) : Γ ⊢ B ⟹ A := 
--   mpon h (exportation weakConj')

-- end DemoExamples