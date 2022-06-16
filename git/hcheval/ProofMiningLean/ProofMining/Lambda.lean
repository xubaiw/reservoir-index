import ProofMining.Term 
import ProofMining.TermPrettyPrinter
import ProofMining.Automation

open Term

set_option print_types false


-- def K₂ (ρ τ : FiniteType) : Term := K (τ ↣ τ) ρ # I τ

-- variable (ρ τ : FiniteType)

-- example : inferType [] (K₂ ρ τ) = (ρ ↣ τ ↣ τ) := by 
--   simp [inferType]

def hasFV (t : Term) (i : Nat) : Bool := match t with 
| var j => i == j 
| app u v => hasFV u i || hasFV v i
| _ => false

/-
  the question remains open. 
  how do we properly define this?
-/

namespace Lambda

def lambda (env : Environment) (src : FiniteType) (t : Term) (σ : FiniteType) (wt : WellTyped (src :: env) t σ := by autowt) : Term := 
match ht:t, hσ:σ, wt with 
| var 0, _, _ => I src 
| var (i + 1), _, _ => K (env.nth i).get!! src # i
| app u v, σ, wt => 
  let σ₁ : FiniteType := Term.getAppSource' wt
  S src σ₁ σ  
    # (lambda env src u (σ₁ ↣ σ) (by {
      cases wt; case _ δ wtv wtu => 
      rw [hσ] at wt; clear hσ
      rw [ht] at wt; clear ht 
      have := (Term.app_source_correct' wt).right 
      rw [(rfl : σ₁ = Term.getAppSource' wt)]
      exact this
    })) 
    # (lambda env src v σ₁ (by{
      cases wt; case _ δ wtv wtu => 
      rw [hσ] at wt; clear hσ
      rw [ht] at wt
      have := (Term.app_source_correct' wt).left
      rw [(rfl : σ₁ = Term.getAppSource' wt)] --nice
      exact this
  }))
| s@(_), _, _ => K (inferType env s).get!! src # s -- NICE. But maybe inconvenient. We'll see
-- | s@(K ρ τ), _, _ => K _ src # s
-- | s@(S ρ τ δ), _, _ => K _ src # s
-- | zero, _, _ => K _ src # zero
-- | successor, _, _ => K _ src # successor
-- | s@(R ρ), _, _ => K _ src # s



def lambda' (env : Environment) (src : FiniteType) (t : Term) : Option Term :=
  let σ? := inferType (src :: env) t 
  match h:σ? with 
  | some σ => lambda env src t σ (by rw [infer_type_iff_well_typed, ←h])
  | none => none 



variable {env : Environment} {src : FiniteType} {t : Term} {ρ σ τ : FiniteType}


def iden : Term := lambda [] 𝕆 0 𝕆 
def proj₂₁ : Term := lambda [] 𝕆 (lambda [𝕆] 𝕆 1 𝕆) (𝕆 ↣ 𝕆) 
def proj₂₂ : Term := lambda [] 𝕆 (lambda [𝕆] 𝕆 0 𝕆) (𝕆 ↣ 𝕆)
def proj₃₁ : Term := lambda [] 𝕆 (lambda [𝕆] 𝕆 (lambda [𝕆, 𝕆] 𝕆 2 𝕆) _) _ -- how does lean figure out the `FiniteType`s here?
def proj₃₂ : Term := lambda [] 𝕆 (lambda [𝕆] 𝕆 (lambda [𝕆, 𝕆] 𝕆 1 𝕆) _) _
def proj₃₃ : Term := lambda [] 𝕆 (lambda [𝕆] 𝕆 (lambda [𝕆, 𝕆] 𝕆 0 𝕆) _) _

/-
  The computational behavior (i.e. excluding typing) seems correct
-/
#reduce iterate reduceOneStep 11 (proj₃₃ # successor # zero # (R 𝕆))
#reduce iterate reduceOneStep 11 (Term.recursorOne 0 # Term.zero # (Lambda.lambda [𝕆] 𝕆 (Lambda.lambda [𝕆, 𝕆] 𝕆 0 𝕆) (𝕆 ↣ 𝕆)) # (Term.var 0) )

-- theorem lambda_fv : hasFV t (i + 1) → hasFV (lambda env src t). i := by 
--   intros hfv 


-- theorem lambda_some : (lambda env src t).isSome := by 
--   induction t 
--   case var i => 
--     cases i 
--     case zero => 
--       simp [lambda, pure, OptionT.pure, OptionT.mk, Option.isSome]
--     case succ j => 
--       simp [lambda, pure, OptionT.pure, OptionT.mk, Option.isSome, bind, OptionT.bind]


set_option print_types true
 
-- theorem lambda_well_typed {env : Environment} {src : FiniteType} (t : Term) (ρ : FiniteType) (wt : WellTyped (src::env) t ρ) :
--   WellTyped env (lambda env src t ρ wt) (src ↣ ρ) := by 
  -- OLD PROOF NO LONGER WORKS
  -- intros h
  -- induction t generalizing ρ
  -- case var i => 
  --   cases i 
  --   case zero => 
  --     cases h; case _ h' => --todo: write tactics for this
  --     -- simp [List.nth] at h'
  --     -- rw [h']
  --     rw [infer_type_iff_well_typed]; simp [List.nth, lambda] at h' ⊢ --todo: write tactic for this
  --     assumption
  --   case succ j => 
  --     cases h; case _ h' => 
  --     simp [List.nth] at h'
  --     simp [lambda]
  --     rw [infer_type_iff_well_typed]
  --     simp [*, Option.get!!]
  -- case app u v ihu ihv =>   
  --   cases h; case _ δ hv hu => 
  --   specialize ihu _ hu
  --   specialize ihv _ hv 
  --   simp [*, lambda]



