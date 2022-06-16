import ProofMining.Formula
import ProofMining.FiniteType
import ProofMining.Term

-- inductive Formula
-- | equality : Term → Term → Formula
-- | conjunction : Formula → Formula → Formula
-- | disjunction : Formula → Formula → Formula
-- | implication : Formula → Formula → Formula
-- | falsum : Formula
-- | universal : FiniteType → Formula → Formula 
-- | existential : FiniteType → Formula → Formula 

open Formula
open FiniteType

variable {x y u v U Y X: FiniteType}

def dialectica (A : Formula) : Formula :=
  match A with
    | equality term₁ term₂ => equality term₁ term₂
    | conjunction A B => ∃∃ x (∃∃ u (∀∀ y (∀∀ v (dialectica A ⋀ dialectica B))))
    | disjunction A B => ∃∃ 0 (∃∃ x (∃∃ u (∀∀ y (∀∀ v 
    (((Term.var 4 ≅ 0) ⟹ dialectica A) ⋀ 
    (∼(Term.var 4 ≅ 0) ⟹ dialectica B))
    ))))
    | implication A B => ∃∃ U (∃∃ Y (∀∀ x (∀∀ v (dialectica A ⟹ dialectica B))))
    | falsum => falsum
    | universal ρ A => ∃∃ X (∀∀ y (∀∀ ρ (dialectica A)))
    | existential ρ A => ∃∃ ρ (∃∃ x (∀∀ y (dialectica A)))
