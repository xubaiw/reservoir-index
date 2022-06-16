import ProofMining.Term 
import ProofMining.TermPrettyPrinter
import ProofMining.Automation

open Term

set_option print_types false



def hasFV (t : Term) (i : Nat) : Bool := match t with 
| var j => i == j 
| app u v => hasFV u i || hasFV v i
| _ => false


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
      rw [(rfl : σ₁ = Term.getAppSource' wt)]
      exact this
  }))
| s@(_), _, _ => K (inferType env s).get!! src # s 


def lambda' (env : Environment) (src : FiniteType) (t : Term) : Option Term :=
  let σ? := inferType (src :: env) t 
  match h:σ? with 
  | some σ => lambda env src t σ (by rw [infer_type_iff_well_typed, ←h])
  | none => none 



variable {env : Environment} {src : FiniteType} {t : Term} {ρ σ τ : FiniteType}


def iden : Term := lambda [] 𝕆 0 𝕆 
def proj₂₁ : Term := lambda [] 𝕆 (lambda [𝕆] 𝕆 1 𝕆) (𝕆 ↣ 𝕆) 
def proj₂₂ : Term := lambda [] 𝕆 (lambda [𝕆] 𝕆 0 𝕆) (𝕆 ↣ 𝕆)
def proj₃₁ : Term := lambda [] 𝕆 (lambda [𝕆] 𝕆 (lambda [𝕆, 𝕆] 𝕆 2 𝕆) _) _ 
def proj₃₂ : Term := lambda [] 𝕆 (lambda [𝕆] 𝕆 (lambda [𝕆, 𝕆] 𝕆 1 𝕆) _) _
def proj₃₃ : Term := lambda [] 𝕆 (lambda [𝕆] 𝕆 (lambda [𝕆, 𝕆] 𝕆 0 𝕆) _) _


#reduce iterate reduceOneStep 11 (proj₃₃ # successor # zero # (R 𝕆))
#reduce iterate reduceOneStep 11 (Term.recursorOne 0 # Term.zero # (Lambda.lambda [𝕆] 𝕆 (Lambda.lambda [𝕆, 𝕆] 𝕆 0 𝕆) (𝕆 ↣ 𝕆)) # (Term.var 0) )



set_option print_types true
 
