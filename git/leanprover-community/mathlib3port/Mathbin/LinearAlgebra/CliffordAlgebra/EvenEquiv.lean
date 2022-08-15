/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathbin.LinearAlgebra.CliffordAlgebra.Even
import Mathbin.LinearAlgebra.QuadraticForm.Prod

/-!
# Isomorphisms with the even subalgebra of a Clifford algebra

This file provides some notable isomorphisms regarding the even subalgebra, `clifford_algebra.even`.

## Main definitions

* `clifford_algebra.equiv_even`: Every Clifford algebra is isomorphic as an algebra to the even
  subalgebra of a Clifford algebra with one more dimension.
  * `clifford_algebra.even_equiv.Q'`: The quadratic form used by this "one-up" algebra.
  * `clifford_algebra.to_even`: The simp-normal form of the forward direction of this isomorphism.
  * `clifford_algebra.of_even`: The simp-normal form of the reverse direction of this isomorphism.

* `clifford_algebra.even_equiv_even_neg`: Every even subalgebra is isomorphic to the even subalgebra
  of the Clifford algebra with negated quadratic form.
  * `clifford_algebra.even_to_neg`: The simp-normal form of each direction of this isomorphism.

## Main results

* `clifford_algebra.coe_to_even_reverse_involute`: the behavior of `clifford_algebra.to_even` on the
  "Clifford conjugate", that is `clifford_algebra.reverse` composed with
  `clifford_algebra.involute`.
-/


namespace CliffordAlgebra

variable {R M : Type _} [CommRingₓ R] [AddCommGroupₓ M] [Module R M]

variable (Q : QuadraticForm R M)

/-! ### Constructions needed for `clifford_algebra.equiv_even` -/


namespace EquivEven

/-- The quadratic form on the augmented vector space `M × R` sending `v + r•e0` to `Q v - r^2`. -/
@[reducible]
def q' : QuadraticForm R (M × R) :=
  Q.Prod <| -@QuadraticForm.sq R _

theorem Q'_apply (m : M × R) : q' Q m = Q m.1 - m.2 * m.2 :=
  (sub_eq_add_neg _ _).symm

/-- The unit vector in the new dimension -/
def e0 : CliffordAlgebra (q' Q) :=
  ι (q' Q) (0, 1)

/-- The embedding from the existing vector space -/
def v : M →ₗ[R] CliffordAlgebra (q' Q) :=
  ι (q' Q) ∘ₗ LinearMap.inl _ _ _

theorem ι_eq_v_add_smul_e0 (m : M) (r : R) : ι (q' Q) (m, r) = v Q m + r • e0 Q := by
  rw [e0, v, LinearMap.comp_apply, LinearMap.inl_apply, ← LinearMap.map_smul, Prod.smul_mk, smul_zero, smul_eq_mul,
    mul_oneₓ, ← LinearMap.map_add, Prod.mk_add_mk, zero_addₓ, add_zeroₓ]

theorem e0_mul_e0 : e0 Q * e0 Q = -1 :=
  (ι_sq_scalar _ _).trans <| by
    simp

theorem v_sq_scalar (m : M) : v Q m * v Q m = algebraMap _ _ (Q m) :=
  (ι_sq_scalar _ _).trans <| by
    simp

theorem neg_e0_mul_v (m : M) : -(e0 Q * v Q m) = v Q m * e0 Q := by
  refine' neg_eq_of_add_eq_zero_right ((ι_mul_ι_add_swap _ _).trans _)
  dsimp' [← QuadraticForm.polar]
  simp only [← add_zeroₓ, ← mul_zero, ← mul_oneₓ, ← zero_addₓ, ← neg_zero, ← QuadraticForm.map_zero, ← add_sub_cancel, ←
    sub_self, ← map_zero, ← zero_sub]

theorem neg_v_mul_e0 (m : M) : -(v Q m * e0 Q) = e0 Q * v Q m := by
  rw [neg_eq_iff_neg_eq]
  exact neg_e0_mul_v _ m

@[simp]
theorem e0_mul_v_mul_e0 (m : M) : e0 Q * v Q m * e0 Q = v Q m := by
  rw [← neg_v_mul_e0, ← neg_mul, mul_assoc, e0_mul_e0, mul_neg_one, neg_negₓ]

@[simp]
theorem reverse_v (m : M) : reverse (v Q m) = v Q m :=
  reverse_ι _

@[simp]
theorem involute_v (m : M) : involute (v Q m) = -v Q m :=
  involute_ι _

@[simp]
theorem reverse_e0 : reverse (e0 Q) = e0 Q :=
  reverse_ι _

@[simp]
theorem involute_e0 : involute (e0 Q) = -e0 Q :=
  involute_ι _

end EquivEven

open EquivEven

/-- The embedding from the smaller algebra into the new larger one. -/
def toEven : CliffordAlgebra Q →ₐ[R] CliffordAlgebra.even (q' Q) := by
  refine' CliffordAlgebra.lift Q ⟨_, fun m => _⟩
  · refine' LinearMap.codRestrict _ _ fun m => Submodule.mem_supr_of_mem ⟨2, rfl⟩ _
    exact (LinearMap.mulLeft R <| e0 Q).comp (v Q)
    rw [Subtype.coe_mk, pow_two]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
    
  · ext1
    dsimp' only [← Subalgebra.coe_mul, ← LinearMap.cod_restrict_apply, ← LinearMap.comp_apply, ←
      LinearMap.mul_left_apply, ← LinearMap.inl_apply, ← Subalgebra.coe_algebra_map]
    rw [← mul_assoc, e0_mul_v_mul_e0, v_sq_scalar]
    

@[simp]
theorem to_even_ι (m : M) : (toEven Q (ι Q m) : CliffordAlgebra (q' Q)) = e0 Q * v Q m := by
  rw [to_even, CliffordAlgebra.lift_ι_apply, LinearMap.cod_restrict_apply]
  rfl

/-- The embedding from the even subalgebra with an extra dimension into the original algebra. -/
def ofEven : CliffordAlgebra.even (q' Q) →ₐ[R] CliffordAlgebra Q := by
  /-
    Recall that we need:
     * `f ⟨0,1⟩ ⟨x,0⟩ = ι x`
     * `f ⟨x,0⟩ ⟨0,1⟩ = -ι x`
     * `f ⟨x,0⟩ ⟨y,0⟩ = ι x * ι y`
     * `f ⟨0,1⟩ ⟨0,1⟩ = -1`
    -/
  let f : M × R →ₗ[R] M × R →ₗ[R] CliffordAlgebra Q :=
    ((Algebra.lmul R (CliffordAlgebra Q)).toLinearMap.comp <|
          (ι Q).comp (LinearMap.fst _ _ _) + (Algebra.linearMap R _).comp (LinearMap.snd _ _ _)).compl₂
      ((ι Q).comp (LinearMap.fst _ _ _) - (Algebra.linearMap R _).comp (LinearMap.snd _ _ _))
  have f_apply : ∀ x y, f x y = (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2) := fun x y => rfl
  have hc : ∀ (r : R) (x : CliffordAlgebra Q), Commute (algebraMap _ _ r) x := Algebra.commutes
  have hm : ∀ m : M × R, ι Q m.1 * ι Q m.1 - algebraMap R _ m.2 * algebraMap R _ m.2 = algebraMap R _ (Q' Q m) := by
    intro m
    rw [ι_sq_scalar, ← RingHom.map_mul, ← RingHom.map_sub, sub_eq_add_neg, Q'_apply, sub_eq_add_neg]
  refine' even.lift (Q' Q) ⟨f, _, _⟩ <;> simp_rw [f_apply]
  · intro m
    rw [← (hc _ _).symm.mul_self_sub_mul_self_eq, hm]
    
  · intro m₁ m₂ m₃
    rw [← mul_smul_comm, ← mul_assoc, mul_assoc (_ + _), ← (hc _ _).symm.mul_self_sub_mul_self_eq', Algebra.smul_def, ←
      mul_assoc, hm]
    

theorem of_even_ι (x y : M × R) :
    ofEven Q ((even.ι _).bilin x y) = (ι Q x.1 + algebraMap R _ x.2) * (ι Q y.1 - algebraMap R _ y.2) :=
  even.lift_ι _ _ _ _

theorem to_even_comp_of_even : (toEven Q).comp (ofEven Q) = AlgHom.id R _ :=
  even.alg_hom_ext (q' Q) <|
    EvenHom.ext _ _ <|
      LinearMap.ext fun m₁ =>
        LinearMap.ext fun m₂ =>
          Subtype.ext <|
            let ⟨m₁, r₁⟩ := m₁
            let ⟨m₂, r₂⟩ := m₂
            calc
              ↑(toEven Q (ofEven Q ((even.ι (q' Q)).bilin (m₁, r₁) (m₂, r₂)))) =
                  (e0 Q * v Q m₁ + algebraMap R _ r₁) * (e0 Q * v Q m₂ - algebraMap R _ r₂) :=
                by
                rw [of_even_ι, AlgHom.map_mul, AlgHom.map_add, AlgHom.map_sub, AlgHom.commutes, AlgHom.commutes,
                  Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_sub, to_even_ι, to_even_ι,
                  Subalgebra.coe_algebra_map, Subalgebra.coe_algebra_map]
              _ =
                  e0 Q * v Q m₁ * (e0 Q * v Q m₂) + r₁ • e0 Q * v Q m₂ - r₂ • e0 Q * v Q m₁ -
                    algebraMap R _ (r₁ * r₂) :=
                by
                rw [mul_sub, add_mulₓ, add_mulₓ, ← Algebra.commutes, ← Algebra.smul_def, ← map_mul, ← Algebra.smul_def,
                  sub_add_eq_sub_sub, smul_mul_assoc, smul_mul_assoc]
              _ = v Q m₁ * v Q m₂ + r₁ • e0 Q * v Q m₂ + v Q m₁ * r₂ • e0 Q + r₁ • e0 Q * r₂ • e0 Q := by
                have h1 : e0 Q * v Q m₁ * (e0 Q * v Q m₂) = v Q m₁ * v Q m₂ := by
                  rw [← mul_assoc, e0_mul_v_mul_e0]
                have h2 : -(r₂ • e0 Q * v Q m₁) = v Q m₁ * r₂ • e0 Q := by
                  rw [mul_smul_comm, smul_mul_assoc, ← smul_neg, neg_e0_mul_v]
                have h3 : -algebraMap R _ (r₁ * r₂) = r₁ • e0 Q * r₂ • e0 Q := by
                  rw [Algebra.algebra_map_eq_smul_one, smul_mul_smul, e0_mul_e0, smul_neg]
                rw [sub_eq_add_neg, sub_eq_add_neg, h1, h2, h3]
              _ = ι _ (m₁, r₁) * ι _ (m₂, r₂) := by
                rw [ι_eq_v_add_smul_e0, ι_eq_v_add_smul_e0, mul_addₓ, add_mulₓ, add_mulₓ, add_assocₓ]
              

theorem of_even_comp_to_even : (ofEven Q).comp (toEven Q) = AlgHom.id R _ :=
  CliffordAlgebra.hom_ext <|
    LinearMap.ext fun m =>
      calc
        ofEven Q (toEven Q (ι Q m)) = ofEven Q ⟨_, (toEven Q (ι Q m)).Prop⟩ := by
          rw [Subtype.coe_eta]
        _ = (ι Q 0 + algebraMap R _ 1) * (ι Q m - algebraMap R _ 0) := by
          simp_rw [to_even_ι]
          exact of_even_ι Q _ _
        _ = ι Q m := by
          rw [map_one, map_zero, map_zero, sub_zero, zero_addₓ, one_mulₓ]
        

/-- Any clifford algebra is isomorphic to the even subalgebra of a clifford algebra with an extra
dimension (that is, with vector space `M × R`), with a quadratic form evaluating to `-1` on that new
basis vector. -/
@[simps]
def equivEven : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra.even (q' Q) :=
  AlgEquiv.ofAlgHom (toEven Q) (ofEven Q) (to_even_comp_of_even Q) (of_even_comp_to_even Q)

/-- The representation of the clifford conjugate (i.e. the reverse of the involute) in the even
subalgebra is just the reverse of the representation. -/
theorem coe_to_even_reverse_involute (x : CliffordAlgebra Q) :
    ↑(toEven Q (reverse (involute x))) = reverse (toEven Q x : CliffordAlgebra (q' Q)) := by
  induction x using CliffordAlgebra.induction
  case h_grade0 r =>
    simp only [← AlgHom.commutes, ← Subalgebra.coe_algebra_map, ← reverse.commutes]
  case h_grade1 m =>
    simp only [← involute_ι, ← Subalgebra.coe_neg, ← to_even_ι, ← reverse.map_mul, ← reverse_v, ← reverse_e0, ←
      reverse_ι, ← neg_e0_mul_v, ← map_neg]
  case h_mul x y hx hy =>
    simp only [← map_mul, ← Subalgebra.coe_mul, ← reverse.map_mul, ← hx, ← hy]
  case h_add x y hx hy =>
    simp only [← map_add, ← Subalgebra.coe_add, ← hx, ← hy]

/-! ### Constructions needed for `clifford_algebra.even_equiv_even_neg` -/


/-- One direction of `clifford_algebra.even_equiv_even_neg` -/
def evenToNeg (Q' : QuadraticForm R M) (h : Q' = -Q) : CliffordAlgebra.even Q →ₐ[R] CliffordAlgebra.even Q' :=
  even.lift Q
    { bilin := -(even.ι Q' : _).bilin,
      contract := fun m => by
        simp_rw [LinearMap.neg_apply, even_hom.contract, h, QuadraticForm.neg_apply, map_neg, neg_negₓ],
      contract_mid := fun m₁ m₂ m₃ => by
        simp_rw [LinearMap.neg_apply, neg_mul_neg, even_hom.contract_mid, h, QuadraticForm.neg_apply, smul_neg,
          neg_smul] }

@[simp]
theorem even_to_neg_ι (Q' : QuadraticForm R M) (h : Q' = -Q) (m₁ m₂ : M) :
    evenToNeg Q Q' h ((even.ι Q).bilin m₁ m₂) = -(even.ι Q').bilin m₁ m₂ :=
  even.lift_ι _ _ m₁ m₂

theorem even_to_neg_comp_even_to_neg (Q' : QuadraticForm R M) (h : Q' = -Q) (h' : Q = -Q') :
    (evenToNeg Q' Q h').comp (evenToNeg Q Q' h) = AlgHom.id R _ := by
  ext m₁ m₂ : 4
  dsimp' only [← even_hom.compr₂_bilin, ← LinearMap.compr₂_apply, ← AlgHom.to_linear_map_apply, ← AlgHom.comp_apply, ←
    AlgHom.id_apply]
  rw [even_to_neg_ι, map_neg, even_to_neg_ι, neg_negₓ]

/-- The even subalgebras of the algebras with quadratic form `Q` and `-Q` are isomorphic.

Stated another way, `𝒞ℓ⁺(p,q,r)` and `𝒞ℓ⁺(q,p,r)` are isomorphic. -/
@[simps]
def evenEquivEvenNeg : CliffordAlgebra.even Q ≃ₐ[R] CliffordAlgebra.even (-Q) :=
  AlgEquiv.ofAlgHom (evenToNeg Q _ rfl) (evenToNeg (-Q) _ (neg_negₓ _).symm) (even_to_neg_comp_even_to_neg _ _ _ _)
    (even_to_neg_comp_even_to_neg _ _ _ _)

end CliffordAlgebra

