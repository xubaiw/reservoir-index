import TBA.While.Semantics

import Aesop
import TBA.Util.AesopExts


namespace While
open State

-- Task 1: The semantic is deterministic.
section task_1

theorem BigstepDeterministic (h₁ : ⟨c, σ⟩ ⇓ σ₁ : t₁) (h₂ : ⟨c, σ⟩ ⇓ σ₂ : t₂)
    : σ₁ = σ₂ ∧ t₁ = t₂ := by
  induction h₁ generalizing σ₂ t₂ with
  | skip | ass => cases h₂ <;> trivial
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq hc₁ hc₂ =>
      have ⟨hσ, _⟩ := ih₁ hc₁
      simp_all [(hσ ▸ ih₂) hc₂]
  | ifTrue _ _ ih | ifFalse _ _ ih => cases h₂ <;> simp_all [ih ‹_›]
  | whileTrue _ _ _ ihc ihind =>
    cases h₂ with
    | whileTrue _ hc hind =>
      have ⟨hσ, _⟩ := ihc hc
      simp_all [(hσ ▸ ihind) hind]
    | whileFalse => simp_all
  | whileFalse => cases h₂ <;> simp_all

end task_1


namespace Optimisation

-- Task 2: Formalisation of constant propagation and folding
section task_2

def foldExpr (σ : State Γ) : Expr Γ τ → Expr Γ τ
  | .const v => Expr.const v
  | .var x h =>
    match σ _ x h with
    | some v => Expr.const v
    | none   => Expr.var x h
  | .binop e₁ op e₂ =>
    match foldExpr σ e₁, foldExpr σ e₂ with
    | .const v₁, .const v₂ => Expr.const (op.eval v₁ v₂)
    | e₁',       e₂'       => Expr.binop e₁' op e₂'

def foldCom (σ : State Γ) : Com Γ → (Com Γ × State Γ)
  | .skip => (Com.skip, σ)
  | .ass x e h =>
      match foldExpr σ e with
      | .const v => (Com.ass x v h, σ[h : x ↦ v])
      | e'       => (Com.ass x e' h, σ[h : x ↦ none])
  | .seq c₁ c₂ =>
    have (c₁', σ')  := foldCom σ c₁
    have (c₂', σ'') := foldCom σ' c₂
    (Com.seq c₁' c₂', σ'')
  | .cond b cₜ cₑ =>
    match foldExpr σ b with
    | .const true  => foldCom σ cₜ
    | .const false => foldCom σ cₑ
    | b' =>
      have ((cₜ', σₜ), (cₑ', σₑ)) := (foldCom σ cₜ, foldCom σ cₑ)
      (Com.cond b' cₜ' cₑ', merge σₜ σₑ)
  | .while b c =>
    match foldExpr σ b with
    | .const false => (Com.skip, σ)
    | _            => (Com.while b (foldCom empty c).1, empty)

def optimise : Com Γ → Com Γ := λ c => (foldCom empty c).1

end task_2


section task_3_and_4

attribute [local simp] foldExpr Nat.add_le_add Nat.le_add_left Nat.le_refl

-- Necessary relation between any optimisation and evaluation state of a program.
-- In short: The optimisation state (ρ) must be a subset of the evaluation state (σ).
abbrev ConstMap {Γ : Ctxt} (σ ρ : State Γ) :=
  ∀ (τ : Ty) (x : VName) (h : Γ x = some τ) (v : Val τ),
    ρ τ x h = some v → σ τ x h = some v

theorem empty_ConstMap : ConstMap σ empty := by
  intro _ _ _ _ _; trivial

theorem foldExprSound (h : ConstMap σ ρ) : Expr.eval σ e = Expr.eval σ (foldExpr ρ e) := by
  induction e with
    rw [foldExpr]
  | var                 => aesop
  | binop _ _ _ ihl ihr =>
    aesop (add norm unfold Expr.eval, safe forward ihl, safe forward ihr)

theorem foldCom_ConstMap (h : ConstMap σ ρ) (hc : ⟨c, σ⟩ ⇓ σ' : t)
    : ConstMap σ' (foldCom ρ c).2 := by
  induction hc generalizing ρ with
    simp only [foldCom]
  | skip => exact h
  | ass =>
    intro _ _ _ _
    aesop (add norm unfold State.update, safe forward foldExprSound)
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | @ifTrue _ b _ _ _ _ _ _ ih | @ifFalse _ b _ _ _ _ _ _ ih =>
    cases hfold : foldExpr ρ b using Expr.bool_rec with
    | htrue | hfalse =>
      first | exact ih h | simp_all [foldExprSound h, Expr.eval]
    | _ =>
      intro _ _ _ _ _
      apply ih h
      aesop (add norm unfold State.merge)
  | @whileTrue _ b =>
    cases hfold : foldExpr ρ b using Expr.bool_rec with
    | hfalse => simp_all [foldExprSound h, Expr.eval]
    | _      => exact empty_ConstMap
  | whileFalse => split <;> first | exact h | exact empty_ConstMap

theorem foldExprEmpty (hfold : foldExpr empty e = Expr.const v)
    : foldExpr σ e = Expr.const v := by
  induction e with
  | const => exact hfold
  | var   => contradiction
  | binop l op r ihl ihr =>
    match hl : foldExpr empty l, hr : foldExpr empty r with
    | .const _, .const _ => simp_all [ihl hl, ihr hr]
    | .var .., _ | _, .var .. | .binop .., _ | _, .binop .. => simp_all

theorem foldExprTime : (Expr.time (foldExpr ρ e)) ≤ (Expr.time e) := by
  induction e <;> aesop (add norm unfold Expr.time)

theorem foldComSoundTime (h : ConstMap σ ρ) (hc : ⟨c, σ⟩ ⇓ σ' : t)
    : ∃ t', ⟨(foldCom ρ c).1, σ⟩ ⇓ σ' : t' ∧ t' ≤ t := by
  induction hc generalizing ρ with
    simp only [foldCom]
  | skip => exact ⟨_, Bigstep.skip, Nat.le_refl _⟩
  | @ass _ _ e =>
    rw [foldExprSound h]
    cases hfold : foldExpr ρ e with
    | _ => exact ⟨_, Bigstep.ass, by simp_all [hfold ▸ foldExprTime]⟩
  | seq hc₁ _ ih₁ ih₂ =>
    have ⟨_, h₁, _⟩ := ih₁ h
    have ⟨_, h₂, _⟩ := ih₂ (foldCom_ConstMap h hc₁)
    exact ⟨_, Bigstep.seq h₁ h₂, by simp_all⟩
  | @ifTrue _ b _ _ _ _ hb _ ih | @ifFalse _ b _ _ _ _ hb _ ih =>
    cases hfold : foldExpr ρ b using Expr.bool_rec with
    | htrue | hfalse =>
      have ⟨_, hc, hle⟩ := ih h
      first | exact ⟨_, hc, Nat.le_step (Nat.le_trans hle (Nat.le_add_left ..))⟩
            | simp_all [foldExprSound h, Expr.eval]
    | _ =>
      rw [foldExprSound h, hfold] at hb
      have ⟨_, hc, _⟩ := ih h
      first | refine ⟨_, Bigstep.ifTrue hb hc, ?_⟩
            | refine ⟨_, Bigstep.ifFalse hb hc, ?_⟩
      simp_all [hfold ▸ foldExprTime]
  | @whileTrue _ b _ _ _ _ _ hb _ _ ihc ihind =>
    cases hfold : foldExpr ρ b using Expr.bool_rec with
    | hfalse => simp_all [foldExprSound h, Expr.eval]
    | _ =>
      cases hfold' : foldExpr empty b using Expr.bool_rec with
      | hfalse => simp_all [foldExprEmpty hfold']
      | _ =>
        have ⟨_, hc, _⟩ := ihc empty_ConstMap
        have ⟨_, hind, _⟩ := ihind empty_ConstMap
        rw [foldCom, hfold'] at hind
        refine ⟨_, Bigstep.whileTrue hb hc hind, ?_⟩
        apply Nat.add_le_add_right <;> simp_all
  | @whileFalse _ b _ hb =>
    cases foldExpr ρ b using Expr.bool_rec with
    | hfalse => exact ⟨_, Bigstep.skip, Nat.le_add_left _ _⟩
    | _      => exact ⟨_, Bigstep.whileFalse hb, Nat.le_refl _⟩

end task_3_and_4


-- Task 3: The optimisation preserves the semantics of a program.
section task_3

theorem foldComSound (h : ConstMap σ ρ) (hc : ⟨c, σ⟩ ⇓ σ' : t)
    : ∃ t', ⟨(foldCom ρ c).1, σ⟩ ⇓ σ' : t' := by
  have ⟨t', hc', _ ⟩ := foldComSoundTime h hc
  exact ⟨t', hc'⟩

-- Main prove that the constant propagation is sound
theorem optimiseSound : ⟨c, σ⟩ ⇓ σ' : t → ∃ t', ⟨optimise c, σ⟩ ⇓ σ' : t' :=
  foldComSound empty_ConstMap

end task_3


-- Task 4: The optimisation does not increase execution time.
section task_4

theorem optimiseTime (h₁ : ⟨c, σ⟩ ⇓ σ' : t₁) (h₂ : ⟨optimise c, σ⟩ ⇓ σ'' : t₂) : t₂ ≤ t₁ := by
  have ⟨_, h₂', hle⟩ := foldComSoundTime empty_ConstMap h₁
  have ⟨_, heq⟩ := BigstepDeterministic h₂ h₂'
  exact heq ▸ hle

end task_4


-- Task 5: The optimisation is idempotent.
section task_5

theorem foldExprIdempotent : foldExpr σ (foldExpr σ e) = foldExpr σ e := by
  induction e <;> aesop (add norm unfold foldExpr)

theorem foldComIdempotent : foldCom σ (foldCom σ c).1 = foldCom σ c := by
  induction c generalizing σ with
    simp only [foldCom]
  | ass _ e =>
    cases hfold : foldExpr σ e with
    | const => rw [foldCom, foldExpr]
    | _     => rw [foldCom, ←hfold, foldExprIdempotent]
  | seq _ _ ihl ihr => rw [ihl, ihr]
  | cond b =>
    cases hfold : foldExpr σ b using Expr.bool_rec with
    | htrue | hfalse => simp_all
    | _ =>
      rw [foldCom, ←hfold, foldExprIdempotent]
      simp_all
  | «while» => split <;> simp_all [foldCom]

-- Main prove that the constant propagation is idempotent (Task 5)
theorem optimiseIdempotent : optimise (optimise c) = optimise c := by
  unfold optimise
  exact congrArg _ foldComIdempotent

end task_5


section task_6

-- Nothing to prove here:
-- 1) Only well-typed Expressions and Programs can be instantiated.
-- 2) Therefore `foldExpr` and `foldCom` may only return well-typed Expressions
--    and Programs by definition. The same also applies to `optimise`.

end task_6

end Optimisation

end While
