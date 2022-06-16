import ProofMining.FiniteType 
import ProofMining.Util


abbrev Environment := List FiniteType


inductive Term 
| var : Nat → Term
| app : Term → Term → Term 
| zero : Term 
| successor : Term 
| kcomb : FiniteType → FiniteType → Term 
| scomb : FiniteType → FiniteType → FiniteType → Term 
| recursorOne: FiniteType → Term
deriving DecidableEq, Inhabited

namespace Term

instance : Coe Nat Term := ⟨var⟩

infixl:80 " # " => app
notation "K" => kcomb
notation "S" => scomb
notation "R" => recursorOne


def shift (place : Nat) (cutoff : Nat := 0) : Term → Term :=
fun term => match term with 
| var i => if i < cutoff then var i else var $ i + place
| app t u => app (t.shift place cutoff) (u.shift place cutoff) 
| zero => zero 
| successor => successor 
| kcomb ρ σ => kcomb ρ σ
| scomb ρ σ τ => scomb ρ σ τ
| recursorOne ρ => recursorOne ρ


def subst : Term → Nat → Term → Term
| var j, i, s => if i = j then s else j
| app t u, i, s => app (t.subst i s) (u.subst i s)
| zero, _, _ => zero 
| successor, _, _ => successor 
| kcomb ρ σ, _, _ => kcomb ρ σ
| scomb ρ σ τ, _, _ => scomb ρ σ τ
| recursorOne ρ, _, _ => recursorOne ρ


inductive WellTyped (env : Environment) : Term → FiniteType → Prop 
| var (i σ) : env.nth i = some σ → WellTyped env (var i) σ 
| app (t u) (ρ τ) : WellTyped env t (ρ ↣ τ) → WellTyped env u ρ → WellTyped env (app t u) τ
| zero : WellTyped env zero 0
| successor : WellTyped env successor 1
| kcomb (ρ σ) : WellTyped env (kcomb ρ σ) (ρ ↣ σ ↣ ρ)
| scomb (ρ σ τ) : WellTyped env (scomb ρ σ τ) ((ρ ↣ σ ↣ τ) ↣ (ρ ↣ σ) ↣ ρ ↣ τ)
| recursorOne ρ : WellTyped env (recursorOne ρ) (ρ ↣ (ρ ↣ 0 ↣ ρ) ↣ 0 ↣ ρ)

notation env " ⊢ʷᵗ " t " : " ρ:max => WellTyped env t ρ



@[simp]
def inferTypeAppAux : Option FiniteType → Option FiniteType → Option FiniteType 
| ρ ↣ τ, σ => if ρ = σ then some τ else none 
| _, _ => none


@[simp]
def inferType : Environment → Term → Option FiniteType
  | env, var x => List.nth env x
  | env, app x y => inferTypeAppAux (inferType env x) (inferType env y)
  | env, zero => some (FiniteType.zero)
  | env, successor => some (FiniteType.zero ↣ FiniteType.zero)
  | env, kcomb ρ σ => some (ρ ↣ σ ↣ ρ)
  | env, scomb ρ σ τ => some ((ρ ↣ σ ↣ τ) ↣ (ρ ↣ σ) ↣ ρ ↣ τ) 
  | env, recursorOne ρ => some $ (ρ ↣ (ρ ↣ 0 ↣ ρ) ↣ 0 ↣ ρ)
  


def getAppSource {env : Environment} {u v : Term} {σ : FiniteType} : 
  inferType env (u # v) = some σ → FiniteType := 
  fun h => let ρ := inferType env u 
  match h':ρ with 
  | ρ₁ ↣ ρ₂ => ρ₁
  | 𝕆 => False.elim (by simp [*] at h)
  | none => False.elim (by simp [*] at h)

theorem app_source_correct {env : Environment} {u v : Term} {σ : FiniteType} (h : inferType env (u # v) = some σ): 
  inferType env v = some (getAppSource h) ∧ inferType env u = some ((getAppSource h) ↣ σ) := sorry

  
  

theorem infer_type_iff_well_typed {env : Environment} {t : Term} {σ : FiniteType} : 
  WellTyped env t σ ↔ inferType env t = some σ := by
  apply Iff.intro
  . intros wt
    induction wt with
    | app _ _ _ _ _ _ h₁ h₂ => 
      simp [inferType, h₂, h₁]
    | var i _ h => 
      simp only [inferType]
      exact h
    | _ => simp only [inferType]
  . intros h
    induction t generalizing σ with
    | var i => 
      simp only [inferType] at h
      constructor
      assumption
    | app u v ihu ihv => 
      have := app_source_correct h
      cases this with | intro hρl hρr => 
      specialize ihu hρr
      specialize ihv hρl
      constructor <;> assumption
    | _ => 
      simp [inferType] at h
      try { rw [←h]; constructor }


@[simp]
def isWellTyped (env : Environment) (t : Term) := Option.isSome $ inferType env t


def getAppSource' {env : Environment} {u v : Term} {σ : FiniteType} : WellTyped env (u # v) σ → FiniteType := 
  fun wt => getAppSource $ infer_type_iff_well_typed.mp wt

theorem app_source_correct' {env : Environment} {u v : Term} {σ : FiniteType} (h : WellTyped env (u # v) σ): 
  WellTyped env v (getAppSource' h) ∧ WellTyped env u (getAppSource' h ↣ σ) := sorry


theorem unique_typing : WellTyped e t ρ → WellTyped e t σ → ρ = σ := by 
  intros wtρ wtσ 
  rw [infer_type_iff_well_typed] at wtρ wtσ 
  have : some ρ = some σ := Eq.trans wtρ.symm wtσ
  cases this
  rfl


theorem subst_well_typed {env} {t s} {ρ σ} {i} : 
  WellTyped env t ρ → env.nth i = some σ → WellTyped env s σ → WellTyped env (t.subst i s) ρ := by 
  intros wtt wti wts 
  induction t generalizing ρ with 
  | var j => 
    byCases h : i = j 
    . rw [h] at wti ⊢
      cases wtt 
      have : some σ = some ρ := Eq.trans wti.symm (by assumption) 
      cases this
      simp [*, subst]
    . simp [*, subst]
  | app u v ihu ihv => 
    cases wtt with 
    | app _ _ τ _ wtu wtv =>
    exact WellTyped.app _ _ _ _ (ihu wtu) (ihv wtv) 
  | _ => 
    simp [*, subst]
#check @subst_well_typed




def idcomb (ρ : FiniteType) : Term := S ρ (0 ↣ ρ) ρ # K ρ (0 ↣ ρ) # K ρ 0
notation "I" => idcomb


@[simp]
def reduceOneStep : Term → Term 
| K _ _ # t # _ => t 
| S _ _ _ # t # u # v => t # v # (u # v)
| t # u => t.reduceOneStep # u.reduceOneStep
| x => x
