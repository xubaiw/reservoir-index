/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.DirectSum.Module
import Mathbin.Algebra.Lie.OfAssociative
import Mathbin.Algebra.Lie.Submodule
import Mathbin.Algebra.Lie.Basic

/-!
# Direct sums of Lie algebras and Lie modules

Direct sums of Lie algebras and Lie modules carry natural algbebra and module structures.

## Tags

lie algebra, lie module, direct sum
-/


universe u v w w₁

namespace DirectSum

open Dfinsupp

open_locale DirectSum

variable {R : Type u} {ι : Type v} [CommRingₓ R]

section Modules

/-! The direct sum of Lie modules over a fixed Lie algebra carries a natural Lie module
structure. -/


variable {L : Type w₁} {M : ι → Type w}

variable [LieRing L] [LieAlgebra R L]

variable [∀ i, AddCommGroupₓ (M i)] [∀ i, Module R (M i)]

variable [∀ i, LieRingModule L (M i)] [∀ i, LieModule R L (M i)]

instance : LieRingModule L (⨁ i, M i) where
  bracket := fun x m => m.map_range (fun i m' => ⁅x,m'⁆) fun i => lie_zero x
  add_lie := fun x y m => by
    ext
    simp only [map_range_apply, add_apply, add_lie]
  lie_add := fun x m n => by
    ext
    simp only [map_range_apply, add_apply, lie_add]
  leibniz_lie := fun x y m => by
    ext
    simp only [map_range_apply, lie_lie, add_apply, sub_add_cancel]

@[simp]
theorem lie_module_bracket_apply (x : L) (m : ⨁ i, M i) (i : ι) : ⁅x,m⁆ i = ⁅x,m i⁆ :=
  map_range_apply _ _ m i

instance : LieModule R L (⨁ i, M i) where
  smul_lie := fun t x m => by
    ext i
    simp only [smul_lie, lie_module_bracket_apply, smul_apply]
  lie_smul := fun t x m => by
    ext i
    simp only [lie_smul, lie_module_bracket_apply, smul_apply]

variable (R ι L M)

/-- The inclusion of each component into a direct sum as a morphism of Lie modules. -/
def lieModuleOf [DecidableEq ι] (j : ι) : M j →ₗ⁅R,L⁆ ⨁ i, M i :=
  { lof R ι M j with
    map_lie' := fun x m => by
      ext i
      by_cases' h : j = i
      · rw [← h]
        simp
        
      · simp [lof, single_eq_of_ne h]
         }

/-- The projection map onto one component, as a morphism of Lie modules. -/
def lieModuleComponent (j : ι) : (⨁ i, M i) →ₗ⁅R,L⁆ M j :=
  { component R ι M j with
    map_lie' := fun x m => by
      simp only [component, lapply_apply, lie_module_bracket_apply, LinearMap.to_fun_eq_coe] }

end Modules

section Algebras

/-! The direct sum of Lie algebras carries a natural Lie algebra structure. -/


variable (L : ι → Type w)

variable [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

instance lieRing : LieRing (⨁ i, L i) :=
  { (inferInstance : AddCommGroupₓ _) with bracket := zipWith (fun i => fun x y => ⁅x,y⁆) fun i => lie_zero 0,
    add_lie := fun x y z => by
      ext
      simp only [zip_with_apply, add_apply, add_lie],
    lie_add := fun x y z => by
      ext
      simp only [zip_with_apply, add_apply, lie_add],
    lie_self := fun x => by
      ext
      simp only [zip_with_apply, add_apply, lie_self, zero_apply],
    leibniz_lie := fun x y z => by
      ext
      simp only [sub_apply, zip_with_apply, add_apply, zero_apply]
      apply leibniz_lie }

@[simp]
theorem bracket_apply (x y : ⨁ i, L i) (i : ι) : ⁅x,y⁆ i = ⁅x i,y i⁆ :=
  zip_with_apply _ _ x y i

instance lieAlgebra : LieAlgebra R (⨁ i, L i) :=
  { (inferInstance : Module R _) with
    lie_smul := fun c x y => by
      ext
      simp only [zip_with_apply, smul_apply, bracket_apply, lie_smul] }

variable (R ι L)

/-- The inclusion of each component into the direct sum as morphism of Lie algebras. -/
@[simps]
def lieAlgebraOf [DecidableEq ι] (j : ι) : L j →ₗ⁅R⁆ ⨁ i, L i :=
  { lof R ι L j with toFun := of L j,
    map_lie' := fun x y => by
      ext i
      by_cases' h : j = i
      · rw [← h]
        simp [of]
        
      · simp [of, single_eq_of_ne h]
         }

/-- The projection map onto one component, as a morphism of Lie algebras. -/
@[simps]
def lieAlgebraComponent (j : ι) : (⨁ i, L i) →ₗ⁅R⁆ L j :=
  { component R ι L j with toFun := component R ι L j,
    map_lie' := fun x y => by
      simp only [component, bracket_apply, lapply_apply, LinearMap.to_fun_eq_coe] }

@[ext]
theorem lie_algebra_ext {x y : ⨁ i, L i} (h : ∀ i, lieAlgebraComponent R ι L i x = lieAlgebraComponent R ι L i y) :
    x = y :=
  Dfinsupp.ext h

include R

theorem lie_of_of_ne [DecidableEq ι] {i j : ι} (hij : j ≠ i) (x : L i) (y : L j) : ⁅of L i x,of L j y⁆ = 0 := by
  apply lie_algebra_ext R ι L
  intro k
  rw [LieHom.map_lie]
  simp only [component, of, lapply_apply, single_add_hom_apply, lie_algebra_component_apply, single_apply, zero_apply]
  by_cases' hik : i = k
  · simp only [dif_neg, not_false_iff, lie_zero, hik.symm, hij]
    
  · simp only [dif_neg, not_false_iff, zero_lie, hik]
    

theorem lie_of_of_eq [DecidableEq ι] {i j : ι} (hij : j = i) (x : L i) (y : L j) :
    ⁅of L i x,of L j y⁆ = of L i ⁅x,hij.recOn y⁆ := by
  have : of L j y = of L i (hij.rec_on y) := Eq.drec (Eq.refl _) hij
  rw [this, ← lie_algebra_of_apply R ι L i ⁅x,hij.rec_on y⁆, LieHom.map_lie, lie_algebra_of_apply, lie_algebra_of_apply]

@[simp]
theorem lie_of [DecidableEq ι] {i j : ι} (x : L i) (y : L j) :
    ⁅of L i x,of L j y⁆ = if hij : j = i then lieAlgebraOf R ι L i ⁅x,hij.recOn y⁆ else 0 := by
  by_cases' hij : j = i
  · simp only [lie_of_of_eq R ι L hij x y, hij, dif_pos, not_false_iff, lie_algebra_of_apply]
    
  · simp only [lie_of_of_ne R ι L hij x y, hij, dif_neg, not_false_iff]
    

variable {R L ι}

/-- Given a family of Lie algebras `L i`, together with a family of morphisms of Lie algebras
`f i : L i →ₗ⁅R⁆ L'` into a fixed Lie algebra `L'`, we have a natural linear map:
`(⨁ i, L i) →ₗ[R] L'`. If in addition `⁅f i x, f j y⁆ = 0` for any `x ∈ L i` and `y ∈ L j` (`i ≠ j`)
then this map is a morphism of Lie algebras. -/
@[simps]
def toLieAlgebra [DecidableEq ι] (L' : Type w₁) [LieRing L'] [LieAlgebra R L'] (f : ∀ i, L i →ₗ⁅R⁆ L')
    (hf : ∀ i j : ι, i ≠ j → ∀ x : L i y : L j, ⁅f i x,f j y⁆ = 0) : (⨁ i, L i) →ₗ⁅R⁆ L' :=
  { /- The goal is linear in `y`. We can use this to reduce to the case that `y` has only one
              non-zero component. -/
      -- Similarly, we can reduce to the case that `x` has only one non-zero component. 
      -- Tidy up and use `lie_of`. 
      -- And finish with trivial case analysis.
      toModule
      R ι L' fun i => (f i : L i →ₗ[R] L') with
    toFun := toModule R ι L' fun i => (f i : L i →ₗ[R] L'),
    map_lie' := fun x y => by
      let f' := fun i => (f i : L i →ₗ[R] L')
      suffices
        ∀ i : ι y : L i, to_module R ι L' f' ⁅x,of L i y⁆ = ⁅to_module R ι L' f' x,to_module R ι L' f' (of L i y)⁆ by
        simp only [← LieAlgebra.ad_apply R]
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
        congr
        clear y
        ext i y
        exact this i y
      suffices
        ∀ i j y : L i x : L j,
          to_module R ι L' f' ⁅of L j x,of L i y⁆ = ⁅to_module R ι L' f' (of L j x),to_module R ι L' f' (of L i y)⁆
        by
        intro i y
        rw [← lie_skew x, ← lie_skew (to_module R ι L' f' x)]
        simp only [LinearMap.map_neg, neg_inj, ← LieAlgebra.ad_apply R]
        rw [← LinearMap.comp_apply, ← LinearMap.comp_apply]
        congr
        clear x
        ext j x
        exact this j i x y
      intro i j y x
      simp only [lie_of R, lie_algebra_of_apply, LieHom.coe_to_linear_map, to_add_monoid_of,
        coe_to_module_eq_coe_to_add_monoid, LinearMap.to_add_monoid_hom_coe]
      rcases eq_or_ne i j with (h | h)
      · have h' : f j (h.rec_on y) = f i y := Eq.drec (Eq.refl _) h
        simp only [h, h', LieHom.coe_to_linear_map, dif_pos, LieHom.map_lie, to_add_monoid_of,
          LinearMap.to_add_monoid_hom_coe]
        
      · simp only [h, hf j i h.symm x y, dif_neg, not_false_iff, AddMonoidHom.map_zero]
         }

end Algebras

section Ideals

variable {L : Type w} [LieRing L] [LieAlgebra R L] (I : ι → LieIdeal R L)

/-- Given a Lie algebra `L` and a family of ideals `I i ⊆ L`, informally this definition is the
statement that `L = ⨁ i, I i`.

More formally, the inclusions give a natural map from the (external) direct sum to the enclosing Lie
algebra: `(⨁ i, I i) → L`, and this definition is the proposition that this map is bijective. -/
def LieAlgebraIsInternal [DecidableEq ι] : Prop :=
  Function.Bijective <| (toModule R ι L) fun i => ((I i).incl : I i →ₗ[R] L)

/-- The fact that this instance is necessary seems to be a bug in typeclass inference. See
[this Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/
Typeclass.20resolution.20under.20binders/near/245151099). -/
instance lieRingOfIdeals : LieRing (⨁ i, I i) :=
  DirectSum.lieRing fun i => ↥(I i)

/-- See `direct_sum.lie_ring_of_ideals` comment. -/
instance lieAlgebraOfIdeals : LieAlgebra R (⨁ i, I i) :=
  DirectSum.lieAlgebra fun i => ↥(I i)

end Ideals

end DirectSum

