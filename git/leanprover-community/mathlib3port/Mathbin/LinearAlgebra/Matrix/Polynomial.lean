/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathbin.Algebra.Polynomial.BigOperators
import Mathbin.Data.Polynomial.Degree.Lemmas
import Mathbin.Data.Polynomial.Eval
import Mathbin.Data.Polynomial.Monic
import Mathbin.LinearAlgebra.Matrix.Determinant

/-!
# Matrices of polynomials and polynomials of matrices

In this file, we prove results about matrices over a polynomial ring.
In particular, we give results about the polynomial given by
`det (t * I + A)`.

## References

  * "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3

## Tags

matrix determinant, polynomial
-/


open Matrix BigOperators Polynomial

variable {n α : Type _} [DecidableEq n] [Fintype n] [CommRingₓ α]

open Polynomial Matrix Equivₓ.Perm

namespace Polynomial

theorem nat_degree_det_X_add_C_le (A B : Matrix n n α) :
    natDegree (det ((x : α[X]) • A.map c + B.map c)) ≤ Fintype.card n := by
  rw [det_apply]
  refine' (nat_degree_sum_le _ _).trans _
  refine' Multiset.max_nat_le_of_forall_le _ _ _
  simp only [forall_apply_eq_imp_iff', true_andₓ, Function.comp_app, Multiset.map_map, Multiset.mem_map,
    exists_imp_distrib, Finset.mem_univ_val]
  intro g
  calc
    nat_degree (sign g • ∏ i : n, (X • A.map C + B.map C) (g i) i) ≤
        nat_degree (∏ i : n, (X • A.map C + B.map C) (g i) i) :=
      by
      cases' Int.units_eq_one_or (sign g) with sg sg
      · rw [sg, one_smul]
        
      · rw [sg, Units.neg_smul, one_smul, nat_degree_neg]
        _ ≤ ∑ i : n, nat_degree (((X : α[X]) • A.map C + B.map C) (g i) i) :=
      nat_degree_prod_le (Finset.univ : Finset n) fun i : n =>
        (X • A.map C + B.map C) (g i) i _ ≤ finset.univ.card • 1 :=
      Finset.sum_le_card_nsmul _ _ 1 fun _ => _ _ ≤ Fintype.card n := by
      simpa
  calc
    nat_degree (((X : α[X]) • A.map C + B.map C) (g i) i) = nat_degree ((X : α[X]) * C (A (g i) i) + C (B (g i) i)) :=
      by
      simp _ ≤ max (nat_degree ((X : α[X]) * C (A (g i) i))) (nat_degree (C (B (g i) i))) :=
      nat_degree_add_le _ _ _ = nat_degree ((X : α[X]) * C (A (g i) i)) :=
      max_eq_leftₓ ((nat_degree_C _).le.trans (zero_le _))_ ≤ nat_degree (X : α[X]) := nat_degree_mul_C_le _ _ _ ≤ 1 :=
      nat_degree_X_le

theorem coeff_det_X_add_C_zero (A B : Matrix n n α) : coeff (det ((x : α[X]) • A.map c + B.map c)) 0 = det B := by
  rw [det_apply, finset_sum_coeff, det_apply]
  refine' Finset.sum_congr rfl _
  intro g hg
  convert coeff_smul (sign g) _ 0
  rw [coeff_zero_prod]
  refine' Finset.prod_congr rfl _
  simp

theorem coeff_det_X_add_C_card (A B : Matrix n n α) :
    coeff (det ((x : α[X]) • A.map c + B.map c)) (Fintype.card n) = det A := by
  rw [det_apply, det_apply, finset_sum_coeff]
  refine' Finset.sum_congr rfl _
  simp only [Algebra.id.smul_eq_mul, Finset.mem_univ, RingHom.map_matrix_apply, forall_true_left, map_apply,
    Pi.smul_apply]
  intro g
  convert coeff_smul (sign g) _ _
  rw [← mul_oneₓ (Fintype.card n)]
  convert (coeff_prod_of_nat_degree_le _ _ _ _).symm
  · ext
    simp [coeff_C]
    
  · intro p hp
    refine' (nat_degree_add_le _ _).trans _
    simpa only [Pi.smul_apply, map_apply, Algebra.id.smul_eq_mul, X_mul_C, nat_degree_C, max_eq_leftₓ, zero_le'] using
      (nat_degree_C_mul_le _ _).trans nat_degree_X_le
    

theorem leading_coeff_det_X_one_add_C (A : Matrix n n α) :
    leadingCoeff (det ((x : α[X]) • (1 : Matrix n n α[X]) + A.map c)) = 1 := by
  cases subsingleton_or_nontrivial α
  · simp
    
  rw [← @det_one n, ← coeff_det_X_add_C_card _ A, leading_coeff]
  simp only [Matrix.map_one, C_eq_zero, RingHom.map_one]
  cases' (nat_degree_det_X_add_C_le 1 A).eq_or_lt with h h
  · simp only [RingHom.map_one, Matrix.map_one, C_eq_zero] at h
    rw [h]
    
  · -- contradiction. we have a hypothesis that the degree is less than |n|
    -- but we know that coeff _ n = 1
    have H := coeff_eq_zero_of_nat_degree_lt h
    rw [coeff_det_X_add_C_card] at H
    simpa using H
    

end Polynomial

