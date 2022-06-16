import ProofMining.Term


inductive Formula
| equality : Term → Term → Formula
| conjunction : Formula → Formula → Formula
| disjunction : Formula → Formula → Formula
| implication : Formula → Formula → Formula
| falsum : Formula
| universal : FiniteType → Formula → Formula 
| existential : FiniteType → Formula → Formula 
deriving DecidableEq, Inhabited


namespace Formula

infix:100 "≅" => equality
infixl:55 " ⋀ " => conjunction
infixl:55 " ⋁ " => disjunction
infixr:50 " ⟹ " => implication
notation "∀∀" => universal
notation "∃∃" => existential

abbrev negation (A) := A ⟹ falsum

prefix:max "∼" => negation

@[appUnexpander universal] def unexpandUniversal : Lean.PrettyPrinter.Unexpander 
| `(universal $ρ $A) => `(∀∀ $ρ $A)
| _ => throw ()

@[appUnexpander existential] def unexpandExistential : Lean.PrettyPrinter.Unexpander 
| `(existential $ρ $A) => `(∃∃ $ρ $A)
| _ => throw ()

def shift (place : Nat) (cutoff : Nat := 0) : Formula → Formula := 
fun A => match cutoff, A with 
| c, t ≅ u => t.shift place c ≅ u.shift place c 
| c, A ⋀ B => A.shift place c ⋀ B.shift place c
| c, A ⋁ B => A.shift place c ⋁ B.shift place c
| c, A ⟹ B => A.shift place c ⟹ B.shift place c
| _, falsum => falsum
| c, universal ρ A => universal ρ $ A.shift place $ c + 1
| c, existential ρ A => existential ρ $ A.shift place $ c + 1

def subst : Formula → Nat → Term → Formula 
| t ≅ u, i, s => t.subst i s ≅ u.subst i s
| A ⋀ B, i, s => A.subst i s ⋀ B.subst i s
| A ⋁ B, i, s => A.subst i s ⋁ B.subst i s
| A ⟹ B, i, s => A.subst i s ⟹ B.subst i s
| falsum, _, _ => falsum
| universal ρ A, i, s => universal ρ $ A.subst (i + 1) (s.shift (place := 1))
| existential ρ A, i, s => existential ρ $ A.subst (i + 1) (s.shift (place := 1))


open Term in
inductive WellFormed : Environment → Formula → Prop 
| equality : WellTyped e t 0 → WellTyped e u 0 → WellFormed e (t ≅ u)
| conjunction (A B) : WellFormed e A → WellFormed e B → WellFormed e (A ⋀ B)
| disjunction (A B) : WellFormed e A → WellFormed e B → WellFormed e (A ⋁ B)
| implication (A B) : WellFormed e A → WellFormed e B → WellFormed e (A ⟹ B)
| universal (A) : WellFormed (ρ :: e) A → WellFormed e (∀∀ ρ A)
| existential (A) : WellFormed (ρ :: e) A → WellFormed e (∃∃ ρ A)
| falsum : WellFormed e falsum

notation e " ⊢ʷᶠ " A:max => WellFormed e A

def highereq : FiniteType → Term → Term → Formula
| ρ ↣ τ, s, t => universal ρ (highereq τ (Term.app (s.shift 1) $ Term.var $ 0) (Term.app (t.shift 1) $ Term.var $ 0))
| 0, s, t => equality s t


def isWellFormed (env : Environment) (A : Formula) : Bool := match env, A with 
| e, t ≅ s => Term.inferType env t = some 𝕆 && Term.inferType env s = some 𝕆
| e, A ⋀ B => isWellFormed env A && isWellFormed env B 
| e, A ⋁ B => isWellFormed env A && isWellFormed env B 
| e, A ⟹ B => isWellFormed env A && isWellFormed env B 
| e, ∀∀ σ A => isWellFormed (σ :: e) A
| e, ∃∃ σ A => isWellFormed (σ :: e) A
| _, falsum => true 


#check @propext
#check @Decidable.rec
#check decide
#check Option.isSome (some 0)
#eval Option.isSome (some 0)
#print Decidable

@[simp]
theorem bool_and_iff_prop_and {x y : Bool} : (x && y) = true ↔ x = true ∧ y = true := by 
  cases x <;> cases y <;> simp


#check decide

theorem well_formed_iff_is_well_formed {env} {A} : WellFormed env A ↔ isWellFormed env A := by
  apply Iff.intro
  . intros h
    induction h with
    | @equality env u v hu hv =>
      simp only [isWellFormed]
      rw [Term.infer_type_iff_well_typed] at hu hv
      simp [hu, hv]
      apply And.intro <;> exact decide_eq_true (by assumption)
    | _ => simp only [isWellFormed, *]
  . intros h
    induction A generalizing env with
    | equality a b =>
      simp only [isWellFormed, bool_and_iff_prop_and] at h      
      cases h with | intro l r =>
      constructor <;> { rw [Term.infer_type_iff_well_typed]; exact of_decide_eq_true (by assumption) }
    | conjunction A B h1 h2 =>
      simp only [isWellFormed, bool_and_iff_prop_and] at h
      cases h with | intro l r =>
      have h3 := h1 l
      have h4 := h2 r
      exact WellFormed.conjunction A B h3 h4
    | disjunction A B h1 h2 =>
      simp only [isWellFormed, bool_and_iff_prop_and] at h
      cases h with | intro l r =>
      have h3 := h1 l
      have h4 := h2 r
      exact WellFormed.disjunction A B h3 h4
    | implication A B h1 h2 =>
      simp only [isWellFormed, bool_and_iff_prop_and] at h
      cases h with | intro l r =>
      have h3 := h1 l
      have h4 := h2 r
      exact WellFormed.implication A B h3 h4
    | universal ρ A h1 =>
      simp only [isWellFormed] at h
      constructor
      specialize h1 h
      exact h1
    | existential ρ A h1 =>
      simp only [isWellFormed] at h
      constructor
      specialize h1 h
      exact h1
    | falsum => 
      constructor  

instance {env : Environment} {A : Formula} : Decidable $ WellFormed env A := 
  if h : isWellFormed env A
    then Decidable.isTrue (by rw [well_formed_iff_is_well_formed]; exact h) 
    else Decidable.isFalse (by rw [well_formed_iff_is_well_formed]; exact h)


-- theorem subst_well_formed {env : Environment} {A : Formula} {i : Nat} {t : Term} {ρ : FiniteType} : 
--   WellFormed env A → env.nth i = some ρ → Term.WellTyped env t ρ → WellFormed env (A.subst i t) := TODO_ALEX

-- theorem weakening {e₁ e₂ : Environment} {A : Formula} : List.Embedding e₁ e₂ → WellFormed e₁ A → WellFormed e₂ A := TODO_ALEX