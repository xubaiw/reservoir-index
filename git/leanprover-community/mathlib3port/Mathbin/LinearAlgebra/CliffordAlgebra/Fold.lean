/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Recursive computation rules for the Clifford algebra

This file provides API for a special case `clifford_algebra.foldr` of the universal property
`clifford_algebra.lift` with `A = module.End R N` for some arbitrary module `N`. This specialization
resembles the `list.foldr` operation, allowing a bilinear map to be "folded" along the generators.

For convenience, this file also provides `clifford_algebra.foldl`, implemented via
`clifford_algebra.reverse`

## Main definitions

* `clifford_algebra.foldr`: a computation rule for building linear maps out of the clifford
  algebra starting on the right, analogous to using `list.foldr` on the generators.
* `clifford_algebra.foldl`: a computation rule for building linear maps out of the clifford
  algebra starting on the left, analogous to using `list.foldl` on the generators.

## Main statements

* `clifford_algebra.right_induction`: an induction rule that adds generators from the right.
* `clifford_algebra.left_induction`: an induction rule that adds generators from the left.
-/


universe u1 u2 u3

variable {R M N : Type _}

variable [CommRingₓ R] [AddCommGroupₓ M] [AddCommGroupₓ N]

variable [Module R M] [Module R N]

variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

section Foldr

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldr Q f hf n (ι Q m * x) = f m (foldr Q f hf n x)`.

For example, `foldr f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)`. -/
def foldr (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) : N →ₗ[R] CliffordAlgebra Q →ₗ[R] N :=
  (CliffordAlgebra.lift Q ⟨f, fun v => LinearMap.ext <| hf v⟩).toLinearMap.flip

@[simp]
theorem foldr_ι (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) (m : M) : foldr Q f hf n (ι Q m) = f m n :=
  LinearMap.congr_fun (lift_ι_apply _ _ _) n

@[simp]
theorem foldr_algebra_map (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) (r : R) : foldr Q f hf n (algebraMap R _ r) = r • n :=
  LinearMap.congr_fun (AlgHom.commutes _ r) n

@[simp]
theorem foldr_one (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) : foldr Q f hf n 1 = n :=
  LinearMap.congr_fun (AlgHom.map_one _) n

@[simp]
theorem foldr_mul (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) (a b : CliffordAlgebra Q) :
    foldr Q f hf n (a * b) = foldr Q f hf (foldr Q f hf n b) a :=
  LinearMap.congr_fun (AlgHom.map_mul _ _ _) n

/-- This lemma demonstrates the origin of the `foldr` name. -/
theorem foldr_prod_map_ι (l : List M) (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) :
    foldr Q f hf n (l.map <| ι Q).Prod = List.foldr (fun m n => f m n) n l := by
  induction' l with hd tl ih
  · rw [List.map_nil, List.prod_nil, List.foldr_nil, foldr_one]
    
  · rw [List.map_cons, List.prod_cons, List.foldr_cons, foldr_mul, foldr_ι, ih]
    

end Foldr

section Foldl

/-- Fold a bilinear map along the generators of a term of the clifford algebra, with the rule
given by `foldl Q f hf n (ι Q m * x) = f m (foldl Q f hf n x)`.

For example, `foldl f hf n (r • ι R u + ι R v * ι R w) = r • f u n + f v (f w n)`. -/
def foldl (f : M →ₗ[R] N →ₗ[R] N) (hf : ∀ m x, f m (f m x) = Q m • x) : N →ₗ[R] CliffordAlgebra Q →ₗ[R] N :=
  LinearMap.compl₂ (foldr Q f hf) reverse

@[simp]
theorem foldl_reverse (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) (x : CliffordAlgebra Q) :
    foldl Q f hf n (reverse x) = foldr Q f hf n x :=
  FunLike.congr_arg (foldr Q f hf n) <| reverse_reverse _

@[simp]
theorem foldr_reverse (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) (x : CliffordAlgebra Q) :
    foldr Q f hf n (reverse x) = foldl Q f hf n x :=
  rfl

@[simp]
theorem foldl_ι (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) (m : M) : foldl Q f hf n (ι Q m) = f m n := by
  rw [← foldr_reverse, reverse_ι, foldr_ι]

@[simp]
theorem foldl_algebra_map (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) (r : R) : foldl Q f hf n (algebraMap R _ r) = r • n := by
  rw [← foldr_reverse, reverse.commutes, foldr_algebra_map]

@[simp]
theorem foldl_one (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) : foldl Q f hf n 1 = n := by
  rw [← foldr_reverse, reverse.map_one, foldr_one]

@[simp]
theorem foldl_mul (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) (a b : CliffordAlgebra Q) :
    foldl Q f hf n (a * b) = foldl Q f hf (foldl Q f hf n a) b := by
  rw [← foldr_reverse, ← foldr_reverse, ← foldr_reverse, reverse.map_mul, foldr_mul]

/-- This lemma demonstrates the origin of the `foldl` name. -/
theorem foldl_prod_map_ι (l : List M) (f : M →ₗ[R] N →ₗ[R] N) hf (n : N) :
    foldl Q f hf n (l.map <| ι Q).Prod = List.foldlₓ (fun m n => f n m) n l := by
  rw [← foldr_reverse, reverse_prod_map_ι, ← List.map_reverse, foldr_prod_map_ι, List.foldr_reverse]

end Foldl

theorem right_induction {P : CliffordAlgebra Q → Prop} (hr : ∀ r : R, P (algebraMap _ _ r))
    (h_add : ∀ x y, P x → P y → P (x + y)) (h_ι_mul : ∀ m x, P x → P (x * ι Q m)) : ∀ x, P x := by
  /- It would be neat if we could prove this via `foldr` like how we prove
    `clifford_algebra.induction`, but going via the grading seems easier. -/
  intro x
  have : x ∈ ⊤ := Submodule.mem_top
  rw [← supr_ι_range_eq_top] at this
  apply Submodule.supr_induction _ this (fun i x hx => _) _ h_add
  · refine' Submodule.pow_induction_on_right _ hr h_add (fun x px m => _) hx
    rintro ⟨m, rfl⟩
    exact h_ι_mul _ _ px
    
  · simpa only [← map_zero] using hr 0
    

theorem left_induction {P : CliffordAlgebra Q → Prop} (hr : ∀ r : R, P (algebraMap _ _ r))
    (h_add : ∀ x y, P x → P y → P (x + y)) (h_mul_ι : ∀ x m, P x → P (ι Q m * x)) : ∀ x, P x := by
  refine' reverse_involutive.surjective.forall.2 _
  intro x
  induction' x using CliffordAlgebra.right_induction with r x y hx hy m x hx
  · simpa only [← reverse.commutes] using hr r
    
  · simpa only [← map_add] using h_add _ _ hx hy
    
  · simpa only [← reverse.map_mul, ← reverse_ι] using h_mul_ι _ _ hx
    

end CliffordAlgebra

