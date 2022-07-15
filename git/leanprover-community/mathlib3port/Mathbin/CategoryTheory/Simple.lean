/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.Abelian.Basic
import Mathbin.CategoryTheory.Subobject.Lattice
import Mathbin.Order.Atoms

/-!
# Simple objects

We define simple objects in any category with zero morphisms.
A simple object is an object `Y` such that any monomorphism `f : X ⟶ Y`
is either an isomorphism or zero (but not both).

This is formalized as a `Prop` valued typeclass `simple X`.

In some contexts, especially representation theory, simple objects are called "irreducibles".

If a morphism `f` out of a simple object is nonzero and has a kernel, then that kernel is zero.
(We state this as `kernel.ι f = 0`, but should add `kernel f ≅ 0`.)

When the category is abelian, being simple is the same as being cosimple (although we do not
state a separate typeclass for this).
As a consequence, any nonzero epimorphism out of a simple object is an isomorphism,
and any nonzero morphism into a simple object has trivial cokernel.

We show that any simple object is indecomposable.
-/


noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroMorphisms C]

/-- An object is simple if monomorphisms into it are (exclusively) either isomorphisms or zero. -/
class Simple (X : C) : Prop where
  mono_is_iso_iff_nonzero : ∀ {Y : C} f : Y ⟶ X [Mono f], IsIso f ↔ f ≠ 0

/-- A nonzero monomorphism to a simple object is an isomorphism. -/
theorem is_iso_of_mono_of_nonzero {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : f ≠ 0) : IsIso f :=
  (Simple.mono_is_iso_iff_nonzero f).mpr w

theorem Simple.of_iso {X Y : C} [Simple Y] (i : X ≅ Y) : Simple X :=
  { mono_is_iso_iff_nonzero := fun Z f m => by
      skip
      have : mono (f ≫ i.hom) := mono_comp _ _
      constructor
      · intro h w
        have j : is_iso (f ≫ i.hom)
        infer_instance
        rw [simple.mono_is_iso_iff_nonzero] at j
        subst w
        simpa using j
        
      · intro h
        have j : is_iso (f ≫ i.hom) := by
          apply is_iso_of_mono_of_nonzero
          intro w
          apply h
          simpa using (cancel_mono i.inv).2 w
        rw [← category.comp_id f, ← i.hom_inv_id, ← category.assoc]
        infer_instance
         }

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem kernel_zero_of_nonzero_from_simple {X Y : C} [Simple X] {f : X ⟶ Y} [HasKernel f] (w : f ≠ 0) :
    kernel.ι f = 0 := by
  classical
  by_contra
  have := is_iso_of_mono_of_nonzero h
  exact w (eq_zero_of_epi_kernel f)

/-- A nonzero morphism `f` to a simple object is an epimorphism
(assuming `f` has an image, and `C` has equalizers).
-/
-- See also `mono_of_nonzero_from_simple`, which requires `preadditive C`.
theorem epi_of_nonzero_to_simple [HasEqualizers C] {X Y : C} [Simple Y] {f : X ⟶ Y} [HasImage f] (w : f ≠ 0) : Epi f :=
  by
  rw [← image.fac f]
  have : is_iso (image.ι f) := is_iso_of_mono_of_nonzero fun h => w (eq_zero_of_image_eq_zero h)
  apply epi_comp

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem mono_to_simple_zero_of_not_iso {X Y : C} [Simple Y] {f : X ⟶ Y} [Mono f] (w : IsIso f → False) : f = 0 := by
  classical
  by_contra
  exact w (is_iso_of_mono_of_nonzero h)

theorem id_nonzero (X : C) [Simple.{v} X] : 𝟙 X ≠ 0 :=
  (Simple.mono_is_iso_iff_nonzero (𝟙 X)).mp
    (by
      infer_instance)

instance (X : C) [Simple.{v} X] : Nontrivial (End X) :=
  nontrivial_of_ne 1 0 (id_nonzero X)

section

theorem Simple.not_is_zero (X : C) [Simple X] : ¬IsZero X := by
  simpa [← limits.is_zero.iff_id_eq_zero] using id_nonzero X

variable [HasZeroObject C]

open ZeroObject

variable (C)

/-- We don't want the definition of 'simple' to include the zero object, so we check that here. -/
theorem zero_not_simple [Simple (0 : C)] : False :=
  (Simple.mono_is_iso_iff_nonzero (0 : (0 : C) ⟶ (0 : C))).mp
    ⟨⟨0, by
        tidy⟩⟩
    rfl

end

end

-- We next make the dual arguments, but for this we must be in an abelian category.
section Abelian

variable [Abelian C]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
/-- In an abelian category, an object satisfying the dual of the definition of a simple object is
    simple. -/
theorem simple_of_cosimple (X : C) (h : ∀ {Z : C} f : X ⟶ Z [Epi f], IsIso f ↔ f ≠ 0) : Simple X :=
  ⟨fun Y f I => by
    classical
    fconstructor
    · intros
      have hx := cokernel.π_of_epi f
      by_contra
      subst h
      exact (h _).mp (cokernel.π_of_zero _ _) hx
      
    · intro hf
      suffices epi f by
        exact is_iso_of_mono_of_epi _
      apply preadditive.epi_of_cokernel_zero
      by_contra h'
      exact cokernel_not_iso_of_nonzero hf ((h _).mpr h')
      ⟩

/-- A nonzero epimorphism from a simple object is an isomorphism. -/
theorem is_iso_of_epi_of_nonzero {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f] (w : f ≠ 0) : IsIso f := by
  -- `f ≠ 0` means that `kernel.ι f` is not an iso, and hence zero, and hence `f` is a mono.
  have : mono f := preadditive.mono_of_kernel_zero (mono_to_simple_zero_of_not_iso (kernel_not_iso_of_nonzero w))
  exact is_iso_of_mono_of_epi f

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem cokernel_zero_of_nonzero_to_simple {X Y : C} [Simple Y] {f : X ⟶ Y} (w : f ≠ 0) : cokernel.π f = 0 := by
  classical
  by_contra h
  have := is_iso_of_epi_of_nonzero h
  exact w (eq_zero_of_mono_cokernel f)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem epi_from_simple_zero_of_not_iso {X Y : C} [Simple X] {f : X ⟶ Y} [Epi f] (w : IsIso f → False) : f = 0 := by
  classical
  by_contra
  exact w (is_iso_of_epi_of_nonzero h)

end Abelian

section Indecomposable

variable [Preadditive C] [HasBinaryBiproducts C]

-- There are another three potential variations of this lemma,
-- but as any one suffices to prove `indecomposable_of_simple` we will not give them all.
theorem Biprod.is_iso_inl_iff_is_zero (X Y : C) : IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ IsZero Y := by
  rw [biprod.is_iso_inl_iff_id_eq_fst_comp_inl, ← biprod.total, add_right_eq_selfₓ]
  constructor
  · intro h
    replace h := h =≫ biprod.snd
    simpa [is_zero.iff_split_epi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] using h
    
  · intro h
    rw [is_zero.iff_split_epi_eq_zero (biprod.snd : X ⊞ Y ⟶ Y)] at h
    rw [h, zero_comp]
    

/-- Any simple object in a preadditive category is indecomposable. -/
theorem indecomposable_of_simple (X : C) [Simple X] : Indecomposable X :=
  ⟨Simple.not_is_zero X, fun Y Z i => by
    refine' or_iff_not_imp_left.mpr fun h => _
    rw [is_zero.iff_split_mono_eq_zero (biprod.inl : Y ⟶ Y ⊞ Z)] at h
    change biprod.inl ≠ 0 at h
    rw [← simple.mono_is_iso_iff_nonzero biprod.inl] at h
    · rwa [biprod.is_iso_inl_iff_is_zero] at h
      
    · exact simple.of_iso i.symm
      
    · infer_instance
      ⟩

end Indecomposable

section Subobject

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

open Subobject

instance {X : C} [Simple X] : Nontrivial (Subobject X) :=
  nontrivial_of_not_is_zero (Simple.not_is_zero X)

instance {X : C} [Simple X] :
    IsSimpleOrder (Subobject X) where eq_bot_or_eq_top := by
    rintro ⟨⟨⟨Y : C, ⟨⟨⟩⟩, f : Y ⟶ X⟩, m : mono f⟩⟩
    skip
    change mk f = ⊥ ∨ mk f = ⊤
    by_cases' h : f = 0
    · exact Or.inl (mk_eq_bot_iff_zero.mpr h)
      
    · refine' Or.inr ((is_iso_iff_mk_eq_top _).mp ((simple.mono_is_iso_iff_nonzero f).mpr h))
      

/-- If `X` has subobject lattice `{⊥, ⊤}`, then `X` is simple. -/
theorem simple_of_is_simple_order_subobject (X : C) [IsSimpleOrder (Subobject X)] : Simple X := by
  constructor
  intros
  constructor
  · intro i
    rw [subobject.is_iso_iff_mk_eq_top] at i
    intro w
    rw [← subobject.mk_eq_bot_iff_zero] at w
    exact IsSimpleOrder.bot_ne_top (w.symm.trans i)
    
  · intro i
    rcases IsSimpleOrder.eq_bot_or_eq_top (subobject.mk f) with (h | h)
    · rw [subobject.mk_eq_bot_iff_zero] at h
      exact False.elim (i h)
      
    · exact (subobject.is_iso_iff_mk_eq_top _).mpr h
      
    

/-- `X` is simple iff it has subobject lattice `{⊥, ⊤}`. -/
theorem simple_iff_subobject_is_simple_order (X : C) : Simple X ↔ IsSimpleOrder (Subobject X) :=
  ⟨by
    intro h
    infer_instance, by
    intro h
    exact simple_of_is_simple_order_subobject X⟩

/-- A subobject is simple iff it is an atom in the subobject lattice. -/
theorem subobject_simple_iff_is_atom {X : C} (Y : Subobject X) : Simple (Y : C) ↔ IsAtom Y :=
  (simple_iff_subobject_is_simple_order _).trans
    ((OrderIso.is_simple_order_iff (subobjectOrderIso Y)).trans Set.is_simple_order_Iic_iff_is_atom)

end Subobject

end CategoryTheory

