import TBA.While.Semantics

import Aesop
import TBA.Util.AesopExts

namespace While

section task1

theorem deterministic: ⟨c,σ⟩ ⇓ σ₁ : t₁ → ⟨c, σ⟩ ⇓ σ₂ : t₂ → t₁ = t₂ ∧ σ₁ = σ₂ := by
  intro h1 h2
  induction h1 generalizing σ₂ t₂ with
  | skip => cases h2 <;> simp
  | ass => cases h2 <;> simp
  | seq _ _ ih₁ ih₂ => cases h2 with | seq hc1 hc2 => 
    have h := ih₁ hc1
    rw[And.right h] at ih₂
    have h' := ih₂ hc2
    simp_all
  | ifTrue _ _ ih | ifFalse _ _ ih => cases h2 <;> simp_all [ih (by assumption)]
  | whileTrue hexpr _ _ ih₁ ih₂ => 
    cases h2 with 
    | whileFalse => simp_all
    | whileTrue _ hc₁' hw' =>
      have h := ih₁ hc₁'
      rw[And.right h] at ih₂
      have h' := ih₂ hw'
      simp_all
  | whileFalse => cases h2 <;> simp_all

end task1

namespace Optimisation




-- Task 1: The semantic is deterministic.
section task_1
-- TODO
theorem semDeterministic : ⟨c, σ⟩ ⇓ σ₁ : t₁ → ⟨c, σ⟩ ⇓ σ₂ : t₂ → ((∀ x, σ₁ x = σ₂ x) ∧  t₁ = t₂) := by
  sorry
end task_1




-- Task 2: Formalisation of constant propagation and folding
section task_2

def foldExpr (σ : State) : Expr → Expr
  | .const v => Expr.const v
  | .var x =>
    match σ x with
    | some v => Expr.const v
    | none   => Expr.var x
  | .binop e₁ op e₂ =>
    match foldExpr σ e₁, foldExpr σ e₂ with
    | .const v₁, .const v₂ =>
      match op.eval v₁ v₂ with
      | some v => Expr.const v
      | none   => Expr.binop v₁ op v₂
    | e₁', e₂' => Expr.binop e₁' op e₂'

def foldCom (σ : State) : Com → (Com × State)
  | .skip => (Com.skip, σ)
  | .ass x e =>
      match foldExpr σ e with
      | .const v => (Com.ass x v, σ[x ↦ v])
      | e'       => (Com.ass x e', σ[x ↦ none])
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
      (Com.cond b' cₜ' cₑ', λ k => if σₜ k = σₑ k then σₜ k else none)
  | .while b c =>
    match foldExpr σ b with
    | .const false => (Com.skip, σ)
    | _            => (Com.while b (foldCom Map.empty c).1, Map.empty)

def optimise : Com → Com := λ c => (foldCom Map.empty c).1


theorem Expr.custom_rec (p : Expr → Prop)
    (htrue : p true) (hfalse : p  false) (hint : ∀ (x : Int), p x)
    (hvar : ∀ (x : VName), p x) (hbinop : ∀ l op r, p (Expr.binop l op r))
    : ∀ v, p v
  | true | false | Val.int _ | .var _ | .binop .. => by simp_all

end task_2




-- Task 3: The optimisation preserves the semantics of a program.
section task_3

abbrev ConstMap (σ ρ : State) := ∀ x v, ρ x = some v → σ x = some v

variable {c : Com} {e : Expr} {σ σ' ρ : State} {t : Nat}

attribute [local simp] foldExpr

theorem empty_ConstMap : ConstMap σ Map.empty := by
  intro _ _ _; trivial

theorem foldExprSound (h : ConstMap σ ρ) : Expr.eval σ e = Expr.eval σ (foldExpr ρ e) := by
  induction e <;> aesop (add norm unfold Expr.eval)

theorem foldCom_ConstMap (h : ConstMap σ ρ) (hc : ⟨c, σ⟩ ⇓ σ' : t)
    : ConstMap σ' (foldCom ρ c).2 := by
  induction hc generalizing ρ with
    simp only [foldCom]
  | skip => exact h
  | ass => intro; aesop (add norm unfold Map.update, safe forward foldExprSound)
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | ifTrue _ _ ih | ifFalse _ _ ih =>
    cases hfold : foldExpr ρ ‹Expr› using Expr.custom_rec with
    | htrue | hfalse =>
      first | exact ih h | simp_all [foldExprSound h, Expr.eval]
    | _ => intro _ _ _; rw [ih h]; aesop
  | whileTrue =>
    cases hfold : foldExpr ρ ‹Expr› using Expr.custom_rec with
    | hfalse => simp_all [foldExprSound h, Expr.eval]
    | _      => exact empty_ConstMap
  | whileFalse => split <;> first | exact h | exact empty_ConstMap

theorem foldExprEmpty (hfold : foldExpr Map.empty e = Expr.const v)
    : foldExpr σ e = Expr.const v := by
  induction e generalizing v with
  | const => rw [←hfold]; rfl
  | var x => simp_all [Map.empty]
  | binop l op r ihl ihr =>
    match hl : foldExpr Map.empty l, hr : foldExpr Map.empty r with
    | .const _, .const _ => simp_all [ihl hl, ihr hr]
    | .var _, _ | _, .var _ | .binop .., _ | _, .binop .. => simp_all

theorem foldComSound (h : ConstMap σ ρ) (hc : ⟨c, σ⟩ ⇓ σ' : t)
    : ∃ t', ⟨(foldCom ρ c).1, σ⟩ ⇓ σ' : t' := by
  induction hc generalizing ρ with
    simp only [foldCom]
  | skip => exact ⟨1, Bigstep.skip⟩
  | ass =>
    rw [foldExprSound h]
    cases foldExpr ρ ‹Expr› <;> exact ⟨_, Bigstep.ass⟩
  | seq hc₁ _ ih₁ ih₂ =>
    match ih₁ h, ih₂ (foldCom_ConstMap h hc₁) with
    | ⟨_, h₁⟩, ⟨_, h₂⟩ => exact ⟨_, Bigstep.seq h₁ h₂⟩
  | ifTrue hb _ ih | ifFalse hb _ ih =>
    cases hfold : foldExpr ρ ‹Expr› using Expr.custom_rec with
    | htrue | hfalse =>
      first | exact ih h | simp_all [foldExprSound h, Expr.eval]
    | _ =>
      rw [foldExprSound h, hfold] at hb
      have ⟨_, hc⟩ := ih h
      first | exact ⟨_, Bigstep.ifTrue hb ‹_›⟩
            | exact ⟨_, Bigstep.ifFalse hb ‹_›⟩
  | whileTrue hb _ _ ihc ihind =>
    rename Expr => b
    cases hfold : foldExpr ρ b using Expr.custom_rec with
    | hfalse => simp_all [foldExprSound h, Expr.eval]
    | _ =>
      cases hfold' : foldExpr Map.empty b using Expr.custom_rec with
      | hfalse => simp_all [foldExprEmpty hfold']
      | _ =>
        have ⟨_, hc⟩ := ihc empty_ConstMap
        have ⟨_, hind⟩ := ihind empty_ConstMap
        rw [foldCom, hfold'] at hind
        exact ⟨_, Bigstep.whileTrue hb hc hind⟩
  | whileFalse hb =>
    cases foldExpr ρ ‹Expr› using Expr.custom_rec with
    | hfalse => exact ⟨_, Bigstep.skip⟩
    | _      => exact ⟨_, Bigstep.whileFalse hb⟩

-- Main prove that the constant propagation is sound (Task 3)
theorem optimiseSound : ⟨c, σ⟩ ⇓ σ' : t → ∃ t', ⟨optimise c, σ⟩ ⇓ σ' : t' := 
  foldComSound empty_ConstMap

end task_3




-- Task 4: The optimisation does not increase execution time.
section task_4

open Nat

variable {c : Com} {e : Expr} {σ σ' ρ : State} {t t₁ t₂ : Nat}

attribute [local simp] foldExpr
attribute [local simp] Nat.le_add_left Nat.le_refl Nat.add_le_add_right Nat.add_le_add_left Nat.add_le_add Nat.zero_le


-- TODO: Make nicer
theorem foldExprTime : (Expr.time (foldExpr σ e)) ≤ (Expr.time e) := by
  induction e with simp only [foldExpr, Expr.time]
  | var x => split <;> simp only [Expr.time]
  | binop e₁ op e₂ h₁ h₂ =>
    cases a : foldExpr σ e₁ with simp_all [Expr.time, add_le_add]
    | const v₁ =>
      cases b : foldExpr σ e₂ with simp_all [Expr.time, add_le_add]
      | const v₂ =>
        split
        simp only [Expr.time, Nat.le_add_left 1 _]
        simp only [Expr.time]
        exact (Nat.add_le_add_right (Nat.add_le_add h₁ h₂) 1)

theorem foldCom_SoundTime (h : ConstMap σ ρ) (hc : ⟨c, σ⟩ ⇓ σ' : t)
    : ∃ t', ⟨(foldCom ρ c).1, σ⟩ ⇓ σ' : t' ∧ t' ≤ t := by
  induction hc generalizing ρ with
    simp only [foldCom]
  | skip => exact ⟨1, ⟨Bigstep.skip, Nat.le_refl 1⟩⟩
  | ass =>
    rw [foldExprSound h]
    cases e' : foldExpr ρ ‹Expr› <;> exact ⟨_, ⟨Bigstep.ass, Nat.add_le_add_right (e' ▸ foldExprTime) 1⟩⟩
  | seq hc₁ _ ih₁ ih₂ =>
    match ih₁ h, ih₂ (foldCom_ConstMap h hc₁) with
    | ⟨t₁, ⟨h₁, le₁⟩⟩, ⟨t₂, ⟨h₂, le₂⟩⟩ =>
      have le := Nat.add_le_add_right (Nat.add_le_add le₁ le₂) 1
      exact ⟨t₁ + t₂ + 1, ⟨Bigstep.seq h₁ h₂, le⟩⟩
  | ifTrue hb _ ih | ifFalse hb _ ih =>
    rename Expr => b
    cases hfold : foldExpr ρ ‹Expr› using Expr.custom_rec with
    | htrue | hfalse =>
      have ⟨w, ⟨hw, hle⟩⟩ := ih h
      have le := Nat.add_le_add (Nat.add_le_add (Nat.zero_le (Expr.time b)) hle) (Nat.zero_le 1)
      simp at le
      first | exact ⟨w, ⟨hw, le⟩⟩
            | simp_all [ih h, foldExprSound h, foldExprTime, Expr.eval]
    | _ =>
      rw [foldExprSound h, hfold] at hb
      have ⟨w, ⟨hw, hle⟩⟩ := ih h
      have le : Expr.time (foldExpr ρ b) + w + 1 ≤ Expr.time b + _ + 1 := Nat.add_le_add (Nat.add_le_add foldExprTime hle) (Nat.le_refl 1)
      rw [hfold] at le
      first | exact ⟨_, ⟨Bigstep.ifTrue hb hw, le⟩⟩
            | exact ⟨_, ⟨Bigstep.ifFalse hb hw, le⟩⟩
  | whileTrue hb _ _ ihc ihind =>
    rename Expr => b
    cases hfold : foldExpr ρ b using Expr.custom_rec with
    | hfalse => simp_all [foldExprSound h, Expr.eval]
    | _ =>
      cases hfold' : foldExpr Map.empty b using Expr.custom_rec with
      | hfalse => simp_all [foldExprEmpty hfold']
      | _ =>
        have ⟨hct, hc⟩ := ihc empty_ConstMap
        have ⟨hindt, hind⟩ := ihind empty_ConstMap
        rw [foldCom, hfold'] at hind
        simp at hind
        have le := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl (Expr.time b)) hc.2) hind.2) (Nat.le_refl 1)
        exact ⟨_, ⟨Bigstep.whileTrue hb hc.1 hind.1, le⟩⟩
  | whileFalse hb =>
    cases foldExpr ρ ‹Expr› using Expr.custom_rec with
    | hfalse => exact ⟨_, ⟨Bigstep.skip, by simp⟩⟩
    | _      => exact ⟨_, ⟨Bigstep.whileFalse hb, Nat.le_refl _⟩⟩


theorem optimise_SoundTime : ⟨c, σ⟩ ⇓ σ' : t → ∃ t', ⟨optimise c, σ⟩ ⇓ σ' : t' ∧ t' ≤ t := 
  foldCom_SoundTime empty_ConstMap


theorem optimiseTime (h₁ : ⟨c, σ⟩ ⇓ σ' : t₁) (h₂ : ⟨optimise c, σ⟩ ⇓ σ' : t₂) : t₂ ≤ t₁ := by
  have ⟨_, ⟨h₂', leq⟩⟩ := optimise_SoundTime h₁
  have ⟨eq, _⟩ := deterministic h₂ h₂'
  exact eq ▸ leq

end task_4




-- Task 5: Constant propagation is idempotent.
section task_5

attribute [local simp] foldExpr
attribute [local simp] foldCom

theorem foldExprIdempotent : foldExpr σ (foldExpr σ e) = foldExpr σ e := by
  induction e <;> aesop

attribute [local simp] foldExprIdempotent


-- TODO: Finalize proof
theorem foldComIdempotent : foldCom σ ((foldCom σ c).1) = foldCom σ c := by
  sorry


theorem optimiseIdempotent : optimise (optimise c) = optimise c := by
  simp_all [optimise]; aesop (add norm foldComIdempotent)

end task_5




-- Task 6: Formalize typing
section task_6

end task_6




end Optimisation


end While
