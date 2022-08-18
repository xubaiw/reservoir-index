/-
Copyright (c) 2022 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Johan Commelin, Reid Barton, Rob Lewis, Joseph Hua
-/
import Mathbin.CategoryTheory.Limits.Final
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms

/-!

# Algebras of endofunctors

This file defines (co)algebras of an endofunctor, and provides the category instance for them.
It also defines the forgetful functor from the category of (co)algebras. It is shown that the
structure map of the initial algebra of an endofunctor is an isomorphism. Furthermore, it is shown
that for an adjunction `F ⊣ G` the category of algebras over `F` is equivalent to the category of
coalgebras over `G`.

## TODO

* Prove the dual result about the structure map of the terminal coalgebra of an endofunctor.
* Prove that if the countable infinite product over the powers of the endofunctor exists, then
  algebras over the endofunctor coincide with algebras over the free monad on the endofunctor.
-/


universe v u

namespace CategoryTheory

namespace Endofunctor

variable {C : Type u} [Category.{v} C]

/-- An algebra of an endofunctor; `str` stands for "structure morphism" -/
structure Algebra (F : C ⥤ C) where
  A : C
  str : F.obj A ⟶ A

instance [Inhabited C] : Inhabited (Algebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Algebra

variable {F : C ⥤ C} (A : Algebra F) {A₀ A₁ A₂ : Algebra F}

/-
```
        str
   F A₀ -----> A₀
    |          |
F f |          | f
    V          V
   F A₁ -----> A₁
        str
```
-/
/-- A morphism between algebras of endofunctor `F` -/
@[ext]
structure Hom (A₀ A₁ : Algebra F) where
  f : A₀.1 ⟶ A₁.1
  h' : F.map f ≫ A₁.str = A₀.str ≫ f := by
    run_tac
      obviously

restate_axiom hom.h'

attribute [simp, reassoc] hom.h

namespace Hom

/-- The identity morphism of an algebra of endofunctor `F` -/
def id : Hom A A where f := 𝟙 _

instance : Inhabited (Hom A A) :=
  ⟨{ f := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
def comp (f : Hom A₀ A₁) (g : Hom A₁ A₂) : Hom A₀ A₂ where f := f.1 ≫ g.1

end Hom

instance (F : C ⥤ C) : CategoryStruct (Algebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[simp]
theorem id_eq_id : Algebra.Hom.id A = 𝟙 A :=
  rfl

@[simp]
theorem id_f : (𝟙 _ : A ⟶ A).1 = 𝟙 A.1 :=
  rfl

variable {A₀ A₁ A₂} (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)

@[simp]
theorem comp_eq_comp : Algebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

/-- Algebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : Category (Algebra F) where

/-- To construct an isomorphism of algebras, it suffices to give an isomorphism of the As which
commutes with the structure morphisms.
-/
@[simps]
def isoMk (h : A₀.1 ≅ A₁.1) (w : F.map h.Hom ≫ A₁.str = A₀.str ≫ h.Hom) : A₀ ≅ A₁ where
  Hom := { f := h.Hom }
  inv :=
    { f := h.inv,
      h' := by
        rw [h.eq_comp_inv, category.assoc, ← w, ← functor.map_comp_assoc]
        simp }

/-- The forgetful functor from the category of algebras, forgetting the algebraic structure. -/
@[simps]
def forget (F : C ⥤ C) : Algebra F ⥤ C where
  obj := fun A => A.1
  map := fun A B f => f.1

/-- An algebra morphism with an underlying isomorphism hom in `C` is an algebra isomorphism. -/
theorem iso_of_iso (f : A₀ ⟶ A₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1,
        h' := by
          rw [is_iso.eq_comp_inv f.1, category.assoc, ← f.h]
          simp },
      by
      tidy⟩⟩

instance forget_reflects_iso : ReflectsIsomorphisms (forget F) where reflects := fun A B => iso_of_iso

instance forget_faithful : Faithful (forget F) where

/-- An algebra morphism with an underlying epimorphism hom in `C` is an algebra epimorphism. -/
theorem epi_of_epi {X Y : Algebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h

/-- An algebra morphism with an underlying monomorphism hom in `C` is an algebra monomorphism. -/
theorem mono_of_mono {X Y : Algebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h

/-- From a natural transformation `α : G → F` we get a functor from
algebras of `F` to algebras of `G`.
-/
@[simps]
def functorOfNatTrans {F G : C ⥤ C} (α : G ⟶ F) : Algebra F ⥤ Algebra G where
  obj := fun A => { A := A.1, str := α.app A.1 ≫ A.str }
  map := fun A₀ A₁ f => { f := f.1 }

/-- The identity transformation induces the identity endofunctor on the category of algebras. -/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp'
          simp ))
    fun X Y f => by
    ext
    dsimp'
    simp

/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans β ⋙ functorOfNatTrans α :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp'
          simp ))
    fun X Y f => by
    ext
    dsimp'
    simp

/-- If `α` and `β` are two equal natural transformations, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) : functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp'
          simp [← h]))
    fun X Y f => by
    ext
    dsimp'
    simp

/-- Naturally isomorphic endofunctors give equivalent categories of algebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Algebra F ≌ Algebra G where
  Functor := functorOfNatTrans α.inv
  inverse := functorOfNatTrans α.Hom
  unitIso :=
    functorOfNatTransId.symm ≪≫
      functorOfNatTransEq
          (by
            simp ) ≪≫
        functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫
      functorOfNatTransEq
          (by
            simp ) ≪≫
        functor_of_nat_trans_id

namespace Initial

variable {A} (h : Limits.IsInitial A)

/-- The inverse of the structure map of an initial algebra -/
@[simp]
def strInv : A.1 ⟶ F.obj A.1 :=
  (h.to ⟨F.obj A.1, F.map A.str⟩).1

theorem left_inv' : (⟨strInv h ≫ A.str⟩ : A ⟶ A) = 𝟙 A :=
  Limits.IsInitial.hom_ext h _ (𝟙 A)

theorem left_inv : strInv h ≫ A.str = 𝟙 _ :=
  congr_arg Hom.f (left_inv' h)

theorem right_inv : A.str ≫ strInv h = 𝟙 _ := by
  rw [str_inv, ← (h.to ⟨F.obj A.1, F.map A.str⟩).h, ← F.map_id, ← F.map_comp]
  congr
  exact left_inv h

/-- The structure map of the inital algebra is an isomorphism,
hence endofunctors preserve their initial algebras
-/
theorem str_is_iso (h : Limits.IsInitial A) : IsIso A.str :=
  { out := ⟨strInv h, right_inv _, left_inv _⟩ }

end Initial

end Algebra

/-- A coalgebra of an endofunctor; `str` stands for "structure morphism" -/
structure Coalgebra (F : C ⥤ C) where
  V : C
  str : V ⟶ F.obj V

instance [Inhabited C] : Inhabited (Coalgebra (𝟭 C)) :=
  ⟨⟨default, 𝟙 _⟩⟩

namespace Coalgebra

variable {F : C ⥤ C} (V : Coalgebra F) {V₀ V₁ V₂ : Coalgebra F}

/-
```
        str
    V₀ -----> F V₀
    |          |
  f |          | F f
    V          V
    V₁ -----> F V₁
        str
```
-/
/-- A morphism between coalgebras of an endofunctor `F` -/
@[ext]
structure Hom (V₀ V₁ : Coalgebra F) where
  f : V₀.1 ⟶ V₁.1
  h' : V₀.str ≫ F.map f = f ≫ V₁.str := by
    run_tac
      obviously

restate_axiom hom.h'

attribute [simp, reassoc] hom.h

namespace Hom

/-- The identity morphism of an algebra of endofunctor `F` -/
def id : Hom V V where f := 𝟙 _

instance : Inhabited (Hom V V) :=
  ⟨{ f := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
def comp (f : Hom V₀ V₁) (g : Hom V₁ V₂) : Hom V₀ V₂ where f := f.1 ≫ g.1

end Hom

instance (F : C ⥤ C) : CategoryStruct (Coalgebra F) where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp _ _ _

@[simp]
theorem id_eq_id : Coalgebra.Hom.id V = 𝟙 V :=
  rfl

@[simp]
theorem id_f : (𝟙 _ : V ⟶ V).1 = 𝟙 V.1 :=
  rfl

variable {V₀ V₁ V₂} (f : V₀ ⟶ V₁) (g : V₁ ⟶ V₂)

@[simp]
theorem comp_eq_comp : Coalgebra.Hom.comp f g = f ≫ g :=
  rfl

@[simp]
theorem comp_f : (f ≫ g).1 = f.1 ≫ g.1 :=
  rfl

/-- Coalgebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : Category (Coalgebra F) where

/-- To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the Vs which
commutes with the structure morphisms.
-/
@[simps]
def isoMk (h : V₀.1 ≅ V₁.1) (w : V₀.str ≫ F.map h.Hom = h.Hom ≫ V₁.str) : V₀ ≅ V₁ where
  Hom := { f := h.Hom }
  inv :=
    { f := h.inv,
      h' := by
        rw [h.eq_inv_comp, ← category.assoc, ← w, category.assoc, ← functor.map_comp]
        simp only [← iso.hom_inv_id, ← Functor.map_id, ← category.comp_id] }

/-- The forgetful functor from the category of coalgebras, forgetting the coalgebraic structure. -/
@[simps]
def forget (F : C ⥤ C) : Coalgebra F ⥤ C where
  obj := fun A => A.1
  map := fun A B f => f.1

/-- A coalgebra morphism with an underlying isomorphism hom in `C` is a coalgebra isomorphism. -/
theorem iso_of_iso (f : V₀ ⟶ V₁) [IsIso f.1] : IsIso f :=
  ⟨⟨{ f := inv f.1,
        h' := by
          rw [is_iso.eq_inv_comp f.1, ← category.assoc, ← f.h, category.assoc]
          simp },
      by
      tidy⟩⟩

instance forget_reflects_iso : ReflectsIsomorphisms (forget F) where reflects := fun A B => iso_of_iso

instance forget_faithful : Faithful (forget F) where

/-- An algebra morphism with an underlying epimorphism hom in `C` is an algebra epimorphism. -/
theorem epi_of_epi {X Y : Coalgebra F} (f : X ⟶ Y) [h : Epi f.1] : Epi f :=
  (forget F).epi_of_epi_map h

/-- An algebra morphism with an underlying monomorphism hom in `C` is an algebra monomorphism. -/
theorem mono_of_mono {X Y : Coalgebra F} (f : X ⟶ Y) [h : Mono f.1] : Mono f :=
  (forget F).mono_of_mono_map h

/-- From a natural transformation `α : F → G` we get a functor from
coalgebras of `F` to coalgebras of `G`.
-/
@[simps]
def functorOfNatTrans {F G : C ⥤ C} (α : F ⟶ G) : Coalgebra F ⥤ Coalgebra G where
  obj := fun V => { V := V.1, str := V.str ≫ α.app V.1 }
  map := fun V₀ V₁ f =>
    { f := f.1,
      h' := by
        rw [category.assoc, ← α.naturality, ← category.assoc, f.h, category.assoc] }

/-- The identity transformation induces the identity endofunctor on the category of coalgebras. -/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransId : functorOfNatTrans (𝟙 F) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp'
          simp ))
    fun X Y f => by
    ext
    dsimp'
    simp

/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransComp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
    functorOfNatTrans (α ≫ β) ≅ functorOfNatTrans α ⋙ functorOfNatTrans β :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp'
          simp ))
    fun X Y f => by
    ext
    dsimp'
    simp

/-- If `α` and `β` are two equal natural transformations, then the functors of coalgebras induced by
them are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps (config := { rhsMd := semireducible })]
def functorOfNatTransEq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) : functorOfNatTrans α ≅ functorOfNatTrans β :=
  NatIso.ofComponents
    (fun X =>
      isoMk (Iso.refl _)
        (by
          dsimp'
          simp [← h]))
    fun X Y f => by
    ext
    dsimp'
    simp

/-- Naturally isomorphic endofunctors give equivalent categories of coalgebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
def equivOfNatIso {F G : C ⥤ C} (α : F ≅ G) : Coalgebra F ≌ Coalgebra G where
  Functor := functorOfNatTrans α.Hom
  inverse := functorOfNatTrans α.inv
  unitIso :=
    functorOfNatTransId.symm ≪≫
      functorOfNatTransEq
          (by
            simp ) ≪≫
        functorOfNatTransComp _ _
  counitIso :=
    (functorOfNatTransComp _ _).symm ≪≫
      functorOfNatTransEq
          (by
            simp ) ≪≫
        functor_of_nat_trans_id

end Coalgebra

namespace Adjunction

variable {F : C ⥤ C} {G : C ⥤ C}

theorem Algebra.hom_equiv_naturality_str (adj : F ⊣ G) (A₁ A₂ : Algebra F) (f : A₁ ⟶ A₂) :
    (adj.homEquiv A₁.A A₁.A) A₁.str ≫ G.map f.f = f.f ≫ (adj.homEquiv A₂.A A₂.A) A₂.str := by
  rw [← adjunction.hom_equiv_naturality_right, ← adjunction.hom_equiv_naturality_left, f.h]

theorem Coalgebra.hom_equiv_naturality_str_symm (adj : F ⊣ G) (V₁ V₂ : Coalgebra G) (f : V₁ ⟶ V₂) :
    F.map f.f ≫ (adj.homEquiv V₂.V V₂.V).symm V₂.str = (adj.homEquiv V₁.V V₁.V).symm V₁.str ≫ f.f := by
  rw [← adjunction.hom_equiv_naturality_left_symm, ← adjunction.hom_equiv_naturality_right_symm, f.h]

/-- Given an adjunction `F ⊣ G`, the functor that associates to an algebra over `F` a
coalgebra over `G` defined via adjunction applied to the structure map. -/
def Algebra.toCoalgebraOf (adj : F ⊣ G) : Algebra F ⥤ Coalgebra G where
  obj := fun A => { V := A.1, str := (adj.homEquiv A.1 A.1).toFun A.2 }
  map := fun A₁ A₂ f => { f := f.1, h' := Algebra.hom_equiv_naturality_str adj A₁ A₂ f }

/-- Given an adjunction `F ⊣ G`, the functor that associates to a coalgebra over `G` an algebra over
`F` defined via adjunction applied to the structure map. -/
def Coalgebra.toAlgebraOf (adj : F ⊣ G) : Coalgebra G ⥤ Algebra F where
  obj := fun V => { A := V.1, str := (adj.homEquiv V.1 V.1).invFun V.2 }
  map := fun V₁ V₂ f => { f := f.1, h' := Coalgebra.hom_equiv_naturality_str_symm adj V₁ V₂ f }

/-- Given an adjunction, assigning to an algebra over the left adjoint a coalgebra over its right
adjoint and going back is isomorphic to the identity functor. -/
def AlgCoalgEquiv.unitIso (adj : F ⊣ G) : 𝟭 (Algebra F) ≅ Algebra.toCoalgebraOf adj ⋙ Coalgebra.toAlgebraOf adj where
  Hom :=
    { app := fun A =>
        { f := 𝟙 A.1,
          h' := by
            erw [F.map_id, category.id_comp, category.comp_id]
            apply (adj.hom_equiv _ _).left_inv A.str },
      naturality' := fun A₁ A₂ f => by
        ext1
        dsimp'
        erw [category.id_comp, category.comp_id]
        rfl }
  inv :=
    { app := fun A =>
        { f := 𝟙 A.1,
          h' := by
            erw [F.map_id, category.id_comp, category.comp_id]
            apply ((adj.hom_equiv _ _).left_inv A.str).symm },
      naturality' := fun A₁ A₂ f => by
        ext1
        dsimp'
        erw [category.comp_id, category.id_comp]
        rfl }
  hom_inv_id' := by
    ext
    exact category.comp_id _
  inv_hom_id' := by
    ext
    exact category.comp_id _

/-- Given an adjunction, assigning to a coalgebra over the right adjoint an algebra over the left
adjoint and going back is isomorphic to the identity functor. -/
def AlgCoalgEquiv.counitIso (adj : F ⊣ G) :
    Coalgebra.toAlgebraOf adj ⋙ Algebra.toCoalgebraOf adj ≅ 𝟭 (Coalgebra G) where
  Hom :=
    { app := fun V =>
        { f := 𝟙 V.1,
          h' := by
            dsimp'
            erw [G.map_id, category.id_comp, category.comp_id]
            apply (adj.hom_equiv _ _).right_inv V.str },
      naturality' := fun V₁ V₂ f => by
        ext1
        dsimp'
        erw [category.comp_id, category.id_comp]
        rfl }
  inv :=
    { app := fun V =>
        { f := 𝟙 V.1,
          h' := by
            dsimp'
            rw [G.map_id, category.comp_id, category.id_comp]
            apply ((adj.hom_equiv _ _).right_inv V.str).symm },
      naturality' := fun V₁ V₂ f => by
        ext1
        dsimp'
        erw [category.comp_id, category.id_comp]
        rfl }
  hom_inv_id' := by
    ext
    exact category.comp_id _
  inv_hom_id' := by
    ext
    exact category.comp_id _

/-- If `F` is left adjoint to `G`, then the category of algebras over `F` is equivalent to the
category of coalgebras over `G`. -/
def algebraCoalgebraEquiv (adj : F ⊣ G) : Algebra F ≌ Coalgebra G where
  Functor := Algebra.toCoalgebraOf adj
  inverse := Coalgebra.toAlgebraOf adj
  unitIso := AlgCoalgEquiv.unitIso adj
  counitIso := AlgCoalgEquiv.counitIso adj
  functor_unit_iso_comp' := fun A => by
    ext
    exact category.comp_id _

end Adjunction

end Endofunctor

end CategoryTheory

