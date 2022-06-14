/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta, Jakob von Raumer
-/
import Mathbin.CategoryTheory.Monoidal.Coherence

/-!
# Lemmas which are consequences of monoidal coherence

These lemmas are all proved `by coherence`.

## Future work
Investigate whether these lemmas are really needed,
or if they can be replaced by use of the `coherence` tactic.
-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Iso

namespace CategoryTheory.MonoidalCategory

variable {C : Type _} [Category C] [MonoidalCategory C]

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
-- See Proposition 2.2.4 of <http://www-math.mit.edu/~etingof/egnobookfinal.pdf>
@[reassoc]
theorem left_unitor_tensor' (X Y : C) : (α_ (𝟙_ C) X Y).Hom ≫ (λ_ (X ⊗ Y)).Hom = (λ_ X).Hom ⊗ 𝟙 Y := by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
@[reassoc, simp]
theorem left_unitor_tensor (X Y : C) : (λ_ (X ⊗ Y)).Hom = (α_ (𝟙_ C) X Y).inv ≫ ((λ_ X).Hom ⊗ 𝟙 Y) := by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
@[reassoc]
theorem left_unitor_tensor_inv (X Y : C) : (λ_ (X ⊗ Y)).inv = ((λ_ X).inv ⊗ 𝟙 Y) ≫ (α_ (𝟙_ C) X Y).Hom := by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
@[reassoc]
theorem id_tensor_right_unitor_inv (X Y : C) : 𝟙 X ⊗ (ρ_ Y).inv = (ρ_ _).inv ≫ (α_ _ _ _).Hom := by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
@[reassoc]
theorem left_unitor_inv_tensor_id (X Y : C) : (λ_ X).inv ⊗ 𝟙 Y = (λ_ _).inv ≫ (α_ _ _ _).inv := by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
@[reassoc]
theorem pentagon_inv_inv_hom (W X Y Z : C) :
    (α_ W (X ⊗ Y) Z).inv ≫ ((α_ W X Y).inv ⊗ 𝟙 Z) ≫ (α_ (W ⊗ X) Y Z).Hom =
      (𝟙 W ⊗ (α_ X Y Z).Hom) ≫ (α_ W X (Y ⊗ Z)).inv :=
  by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
@[simp, reassoc]
theorem triangle_assoc_comp_right_inv (X Y : C) : ((ρ_ X).inv ⊗ 𝟙 Y) ≫ (α_ X (𝟙_ C) Y).Hom = 𝟙 X ⊗ (λ_ Y).inv := by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
theorem unitors_equal : (λ_ (𝟙_ C)).Hom = (ρ_ (𝟙_ C)).Hom := by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
theorem unitors_inv_equal : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
@[reassoc]
theorem pentagon_hom_inv {W X Y Z : C} :
    (α_ W X (Y ⊗ Z)).Hom ≫ (𝟙 W ⊗ (α_ X Y Z).inv) =
      (α_ (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).Hom ⊗ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).Hom :=
  by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

-- ././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence
@[reassoc]
theorem pentagon_inv_hom (W X Y Z : C) :
    (α_ (W ⊗ X) Y Z).inv ≫ ((α_ W X Y).Hom ⊗ 𝟙 Z) =
      (α_ W X (Y ⊗ Z)).Hom ≫ (𝟙 W ⊗ (α_ X Y Z).inv) ≫ (α_ W (X ⊗ Y) Z).inv :=
  by
  "././Mathport/Syntax/Translate/Basic.lean:535:16: unsupported tactic `coherence"

end CategoryTheory.MonoidalCategory

