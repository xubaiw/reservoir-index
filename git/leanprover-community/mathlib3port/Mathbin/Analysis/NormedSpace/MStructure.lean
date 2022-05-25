/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Algebra.Ring.Idempotents
import Mathbin.Tactic.NoncommRing

/-!
# M-structure

A continuous projection `P` on a normed space `X` is said to be an L-projection if, for all `x` in
`X`,
$$
∥x∥ = ∥P x∥ + ∥(1 - P) x∥.
$$

A continuous projection `P` on a normed space `X` is said to be an M-projection if, for all `x` in
`X`,
$$
∥x∥ = max(∥P x∥,∥(1 - P) x∥).
$$

The L-projections on `X` form a Boolean algebra.

## TODO (Motivational background)

The M-projections on a normed space form a Boolean algebra.

The range of an L-projection on a normed space `X` is said to be an L-summand of `X`. The range of
an M-projection is said to be an M-summand of `X`.

When `X` is a Banach space, the Boolean algebra of L-projections is complete. Let `X` be a normed
space with dual `X^*`. A closed subspace `M` of `X` is said to be an M-ideal if the topological
annihilator `M^∘` is an L-summand of `X^*`.

M-ideal, M-summands and L-summands were introduced by Alfsen and Effros in [alfseneffros1972] to
study the structure of general Banach spaces. When `A` is a JB*-triple, the M-ideals of `A` are
exactly the norm-closed ideals of `A`. When `A` is a JBW*-triple with predual `X`, the M-summands of
`A` are exactly the weak*-closed ideals, and their pre-duals can be identified with the L-summands
of `X`. In the special case when `A` is a C*-algebra, the M-ideals are exactly the norm-closed
two-sided ideals of `A`, when `A` is also a W*-algebra the M-summands are exactly the weak*-closed
two-sided ideals of `A`.

## Implementation notes

The approach to showing that the L-projections form a Boolean algebra is inspired by
`measure_theory.measurable_space`.

## References

* [Behrends, M-structure and the Banach-Stone Theorem][behrends1979]
* [Harmand, Werner, Werner, M-ideals in Banach spaces and Banach algebras][harmandwernerwerner1993]

## Tags

M-summand, M-projection, L-summand, L-projection, M-ideal, M-structure

-/


variable {X : Type _} [NormedGroup X]

variable {𝕜 : Type _} [NormedField 𝕜] [NormedSpace 𝕜 X]

/-- A projection on a normed space `X` is said to be an L-projection if, for all `x` in `X`,
$$
∥x∥ = ∥P x∥ + ∥(1 - P) x∥.
$$
-/
structure IsLprojection (P : X →L[𝕜] X) : Prop where
  proj : IsIdempotentElem P
  Lnorm : ∀ x : X, ∥x∥ = ∥P x∥ + ∥(1 - P) x∥

/-- A projection on a normed space `X` is said to be an M-projection if, for all `x` in `X`,
$$
∥x∥ = max(∥P x∥, ∥(1 - P) x∥).
$$
-/
structure IsMprojection (P : X →L[𝕜] X) : Prop where
  proj : IsIdempotentElem P
  Mnorm : ∀ x : X, ∥x∥ = max ∥P x∥ ∥(1 - P) x∥

namespace IsLprojection

theorem Lcomplement {P : X →L[𝕜] X} (h : IsLprojection P) : IsLprojection (1 - P) :=
  ⟨h.proj.one_sub, fun x => by
    rw [add_commₓ, sub_sub_cancel]
    exact h.Lnorm x⟩

theorem Lcomplement_iff (P : X →L[𝕜] X) : IsLprojection P ↔ IsLprojection (1 - P) :=
  ⟨Lcomplement, fun h => sub_sub_cancel 1 P ▸ h.Lcomplement⟩

theorem commute {P Q : X →L[𝕜] X} (h₁ : IsLprojection P) (h₂ : IsLprojection Q) : Commute P Q := by
  have PR_eq_RPR : ∀ R : X →L[𝕜] X, IsLprojection R → P * R = R * P * R := fun R h₃ => by
    ext
    rw [← norm_sub_eq_zero_iff]
    have e1 : ∥R x∥ ≥ ∥R x∥ + 2 • ∥(P * R) x - (R * P * R) x∥ :=
      calc
        ∥R x∥ = ∥R (P (R x))∥ + ∥(1 - R) (P (R x))∥ + (∥(R * R) x - R (P (R x))∥ + ∥(1 - R) ((1 - P) (R x))∥) := by
          rw [h₁.Lnorm, h₃.Lnorm, h₃.Lnorm ((1 - P) (R x)), ContinuousLinearMap.sub_apply 1 P,
            ContinuousLinearMap.one_apply, map_sub, ContinuousLinearMap.coe_mul]
        _ = ∥R (P (R x))∥ + ∥(1 - R) (P (R x))∥ + (∥R x - R (P (R x))∥ + ∥((1 - R) * R) x - (1 - R) (P (R x))∥) := by
          rw [h₃.proj.eq, ContinuousLinearMap.sub_apply 1 P, ContinuousLinearMap.one_apply, map_sub,
            ContinuousLinearMap.coe_mul]
        _ = ∥R (P (R x))∥ + ∥(1 - R) (P (R x))∥ + (∥R x - R (P (R x))∥ + ∥(1 - R) (P (R x))∥) := by
          rw [sub_mul, h₃.proj.eq, one_mulₓ, sub_self, ContinuousLinearMap.zero_apply, zero_sub, norm_neg]
        _ = ∥R (P (R x))∥ + ∥R x - R (P (R x))∥ + 2 • ∥(1 - R) (P (R x))∥ := by
          abel
        _ ≥ ∥R x∥ + 2 • ∥(P * R) x - (R * P * R) x∥ :=
          add_le_add_right (norm_le_insert' (R x) (R (P (R x)))) (2 • ∥(1 - R) (P (R x))∥)
        
    rw [Ge] at e1
    nth_rw_rhs 0[← add_zeroₓ ∥R x∥]  at e1
    rw [add_le_add_iff_left, two_smul, ← two_mul] at e1
    rw [le_antisymm_iffₓ]
    refine' ⟨_, norm_nonneg _⟩
    rwa [← mul_zero (2 : ℝ),
      mul_le_mul_left
        (show (0 : ℝ) < 2 by
          norm_num)] at
      e1
  have QP_eq_QPQ : Q * P = Q * P * Q := by
    have e1 : P * (1 - Q) = P * (1 - Q) - (Q * P - Q * P * Q) :=
      calc
        P * (1 - Q) = (1 - Q) * P * (1 - Q) := by
          rw [PR_eq_RPR (1 - Q) h₂.Lcomplement]
        _ = P * (1 - Q) - (Q * P - Q * P * Q) := by
          noncomm_ring
        
    rwa [eq_sub_iff_add_eq, add_right_eq_selfₓ, sub_eq_zero] at e1
  show P * Q = Q * P
  · rw [QP_eq_QPQ, PR_eq_RPR Q h₂]
    

theorem mul {P Q : X →L[𝕜] X} (h₁ : IsLprojection P) (h₂ : IsLprojection Q) : IsLprojection (P * Q) := by
  refine' ⟨IsIdempotentElem.mul_of_commute (h₁.commute h₂) h₁.proj h₂.proj, _⟩
  intro x
  refine' le_antisymmₓ _ _
  · calc ∥x∥ = ∥(P * Q) x + (x - (P * Q) x)∥ := by
        rw [add_sub_cancel'_right ((P * Q) x) x]_ ≤ ∥(P * Q) x∥ + ∥x - (P * Q) x∥ := by
        apply norm_add_le _ = ∥(P * Q) x∥ + ∥(1 - P * Q) x∥ := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    
  · calc ∥x∥ = ∥P (Q x)∥ + (∥Q x - P (Q x)∥ + ∥x - Q x∥) := by
        rw [h₂.Lnorm x, h₁.Lnorm (Q x), ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
          add_assocₓ]_ ≥ ∥P (Q x)∥ + ∥Q x - P (Q x) + (x - Q x)∥ :=
        (add_le_add_iff_left ∥P (Q x)∥).mpr (norm_add_le (Q x - P (Q x)) (x - Q x))_ = ∥(P * Q) x∥ + ∥(1 - P * Q) x∥ :=
        by
        rw [sub_add_sub_cancel', ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
          ContinuousLinearMap.coe_mul]
    

theorem join {P Q : X →L[𝕜] X} (h₁ : IsLprojection P) (h₂ : IsLprojection Q) : IsLprojection (P + Q - P * Q) := by
  convert (Lcomplement_iff _).mp (h₁.Lcomplement.mul h₂.Lcomplement) using 1
  noncomm_ring

instance : HasCompl { f : X →L[𝕜] X // IsLprojection f } :=
  ⟨fun P => ⟨1 - P, P.Prop.Lcomplement⟩⟩

@[simp]
theorem coe_compl (P : { P : X →L[𝕜] X // IsLprojection P }) : ↑(Pᶜ) = (1 : X →L[𝕜] X) - ↑P :=
  rfl

instance : HasInf { P : X →L[𝕜] X // IsLprojection P } :=
  ⟨fun P Q => ⟨P * Q, P.Prop.mul Q.Prop⟩⟩

@[simp]
theorem coe_inf (P Q : { P : X →L[𝕜] X // IsLprojection P }) : ↑(P⊓Q) = (↑P : X →L[𝕜] X) * ↑Q :=
  rfl

instance : HasSup { P : X →L[𝕜] X // IsLprojection P } :=
  ⟨fun P Q => ⟨P + Q - P * Q, P.Prop.join Q.Prop⟩⟩

@[simp]
theorem coe_sup (P Q : { P : X →L[𝕜] X // IsLprojection P }) : ↑(P⊔Q) = (↑P : X →L[𝕜] X) + ↑Q - ↑P * ↑Q :=
  rfl

instance : HasSdiff { P : X →L[𝕜] X // IsLprojection P } :=
  ⟨fun P Q => ⟨P * (1 - Q), P.prop.mul Q.prop.Lcomplement⟩⟩

@[simp]
theorem coe_sdiff (P Q : { P : X →L[𝕜] X // IsLprojection P }) : ↑(P \ Q) = (↑P : X →L[𝕜] X) * (1 - ↑Q) :=
  rfl

instance : PartialOrderₓ { P : X →L[𝕜] X // IsLprojection P } where
  le := fun P Q => (↑P : X →L[𝕜] X) = ↑(P⊓Q)
  le_refl := fun P => by
    simpa only [coe_inf, ← sq] using P.prop.proj.eq.symm
  le_trans := fun P Q R h₁ h₂ => by
    simp only [coe_inf] at h₁ h₂⊢
    rw [h₁, mul_assoc, ← h₂]
  le_antisymm := fun P Q h₁ h₂ =>
    Subtype.eq
      (by
        convert (P.prop.commute Q.prop).Eq)

theorem le_def (P Q : { P : X →L[𝕜] X // IsLprojection P }) : P ≤ Q ↔ (P : X →L[𝕜] X) = ↑(P⊓Q) :=
  Iff.rfl

instance : Zero { P : X →L[𝕜] X // IsLprojection P } :=
  ⟨⟨0,
      ⟨by
        rw [IsIdempotentElem, zero_mul], fun x => by
        simp only [ContinuousLinearMap.zero_apply, norm_zero, sub_zero, ContinuousLinearMap.one_apply, zero_addₓ]⟩⟩⟩

@[simp]
theorem coe_zero : ↑(0 : { P : X →L[𝕜] X // IsLprojection P }) = (0 : X →L[𝕜] X) :=
  rfl

instance : One { P : X →L[𝕜] X // IsLprojection P } :=
  ⟨⟨1, sub_zero (1 : X →L[𝕜] X) ▸ (0 : { P : X →L[𝕜] X // IsLprojection P }).Prop.Lcomplement⟩⟩

@[simp]
theorem coe_one : ↑(1 : { P : X →L[𝕜] X // IsLprojection P }) = (1 : X →L[𝕜] X) :=
  rfl

instance : BoundedOrder { P : X →L[𝕜] X // IsLprojection P } where
  top := 1
  le_top := fun P =>
    (by
      rw [mul_oneₓ] : (↑P : X →L[𝕜] X) = ↑P * 1)
  bot := 0
  bot_le := fun P => show 0 ≤ P from zero_mul P

@[simp]
theorem coe_bot : ↑(BoundedOrder.bot : { P : X →L[𝕜] X // IsLprojection P }) = (0 : X →L[𝕜] X) :=
  rfl

@[simp]
theorem coe_top : ↑(BoundedOrder.top : { P : X →L[𝕜] X // IsLprojection P }) = (1 : X →L[𝕜] X) :=
  rfl

theorem compl_mul_left {P : { P : X →L[𝕜] X // IsLprojection P }} {Q : X →L[𝕜] X} : Q - ↑P * Q = ↑(Pᶜ) * Q := by
  rw [coe_compl, sub_mul, one_mulₓ]

theorem compl_orthog {P : { P : X →L[𝕜] X // IsLprojection P }} : (↑P : X →L[𝕜] X) * ↑(Pᶜ) = 0 := by
  rw [coe_compl, mul_sub, mul_oneₓ, P.prop.proj.eq, sub_self]

theorem distrib_lattice_lemma {P Q R : { P : X →L[𝕜] X // IsLprojection P }} :
    ((↑P : X →L[𝕜] X) + ↑(Pᶜ) * R) * (↑P + ↑Q * ↑R * ↑(Pᶜ)) = ↑P + ↑Q * ↑R * ↑(Pᶜ) := by
  rw [add_mulₓ, mul_addₓ, mul_addₓ, mul_assoc (↑(Pᶜ)) (↑R) (↑Q * ↑R * ↑(Pᶜ)), ← mul_assoc (↑R) (↑Q * ↑R) ↑(Pᶜ), ←
    coe_inf Q, (Pᶜ.Prop.Commute R.prop).Eq, ((Q⊓R).Prop.Commute Pᶜ.Prop).Eq, (R.prop.commute (Q⊓R).Prop).Eq, coe_inf Q,
    mul_assoc ↑Q, ← mul_assoc, mul_assoc ↑R, (Pᶜ.Prop.Commute P.prop).Eq, compl_orthog, zero_mul, mul_zero, zero_addₓ,
    add_zeroₓ, ← mul_assoc, P.prop.proj.eq, R.prop.proj.eq, ← coe_inf Q, mul_assoc, ((Q⊓R).Prop.Commute Pᶜ.Prop).Eq, ←
    mul_assoc, Pᶜ.Prop.proj.Eq]

instance : DistribLattice { P : X →L[𝕜] X // IsLprojection P } :=
  { IsLprojection.Subtype.hasInf, IsLprojection.Subtype.hasSup, IsLprojection.Subtype.partialOrder with
    le_sup_left := fun P Q => by
      rw [le_def, coe_inf, coe_sup, ← add_sub, mul_addₓ, mul_sub, ← mul_assoc, P.prop.proj.eq, sub_self, add_zeroₓ],
    le_sup_right := fun P Q => by
      rw [le_def, coe_inf, coe_sup, ← add_sub, mul_addₓ, mul_sub, Commute.eq (Commute P.prop Q.prop), ← mul_assoc,
        Q.prop.proj.eq, add_sub_cancel'_right],
    sup_le := fun P Q R => by
      rw [le_def, le_def, le_def, coe_inf, coe_inf, coe_sup, coe_inf, coe_sup, ← add_sub, add_mulₓ, sub_mul, mul_assoc]
      intro h₁ h₂
      rw [← h₂, ← h₁],
    inf_le_left := fun P Q => by
      rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc, (Q.prop.commute P.prop).Eq, ← mul_assoc, P.prop.proj.eq],
    inf_le_right := fun P Q => by
      rw [le_def, coe_inf, coe_inf, coe_inf, mul_assoc, Q.prop.proj.eq],
    le_inf := fun P Q R => by
      rw [le_def, le_def, le_def, coe_inf, coe_inf, coe_inf, coe_inf, ← mul_assoc]
      intro h₁ h₂
      rw [← h₁, ← h₂],
    le_sup_inf := fun P Q R => by
      have e₁ : ↑((P⊔Q)⊓(P⊔R)) = ↑P + ↑Q * ↑R * ↑(Pᶜ) := by
        rw [coe_inf, coe_sup, coe_sup, ← add_sub, ← add_sub, compl_mul_left, compl_mul_left, add_mulₓ, mul_addₓ,
          (Pᶜ.Prop.Commute Q.prop).Eq, mul_addₓ, ← mul_assoc, mul_assoc ↑Q, (Pᶜ.Prop.Commute P.prop).Eq, compl_orthog,
          zero_mul, mul_zero, zero_addₓ, add_zeroₓ, ← mul_assoc, mul_assoc ↑Q, P.prop.proj.eq, Pᶜ.Prop.proj.Eq,
          mul_assoc, (Pᶜ.Prop.Commute R.prop).Eq, ← mul_assoc]
      have e₂ : ↑((P⊔Q)⊓(P⊔R)) * ↑(P⊔Q⊓R) = ↑P + ↑Q * ↑R * ↑(Pᶜ) := by
        rw [coe_inf, coe_sup, coe_sup, coe_sup, ← add_sub, ← add_sub, ← add_sub, compl_mul_left, compl_mul_left,
          compl_mul_left, (Pᶜ.Prop.Commute (Q⊓R).Prop).Eq, coe_inf, mul_assoc, distrib_lattice_lemma,
          (Q.prop.commute R.prop).Eq, distrib_lattice_lemma]
      rw [le_def, e₁, coe_inf, e₂] }

instance : BooleanAlgebra { P : X →L[𝕜] X // IsLprojection P } :=
  { IsLprojection.Subtype.hasCompl, IsLprojection.Subtype.hasSdiff, IsLprojection.Subtype.boundedOrder,
    IsLprojection.Subtype.distribLattice with
    sup_inf_sdiff := fun P Q =>
      Subtype.ext
        (by
          rw [coe_sup, coe_inf, coe_sdiff, mul_assoc, ← mul_assoc ↑Q, (Q.prop.commute P.prop).Eq, mul_assoc ↑P ↑Q, ←
            coe_compl, compl_orthog, mul_zero, mul_zero, sub_zero, ← mul_addₓ, coe_compl, add_sub_cancel'_right,
            mul_oneₓ]),
    inf_inf_sdiff := fun P Q =>
      Subtype.ext
        (by
          rw [coe_inf, coe_inf, coe_sdiff, coe_bot, mul_assoc, ← mul_assoc ↑Q, (Q.prop.commute P.prop).Eq, ← coe_compl,
            mul_assoc, compl_orthog, mul_zero, mul_zero]),
    inf_compl_le_bot := fun P =>
      (Subtype.ext
          (by
            rw [coe_inf, coe_compl, coe_bot, ← coe_compl, compl_orthog])).le,
    top_le_sup_compl := fun P =>
      (Subtype.ext
          (by
            rw [coe_top, coe_sup, coe_compl, add_sub_cancel'_right, ← coe_compl, compl_orthog, sub_zero])).le,
    sdiff_eq := fun P Q =>
      Subtype.ext
        (by
          rw [coe_sdiff, ← coe_compl, coe_inf]) }

end IsLprojection

