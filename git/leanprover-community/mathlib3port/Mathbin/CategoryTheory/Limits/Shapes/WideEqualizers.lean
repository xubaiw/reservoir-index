/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.EpiMono
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Wide equalizers and wide coequalizers

This file defines wide (co)equalizers as special cases of (co)limits.

A wide equalizer for the family of morphisms `X ⟶ Y` indexed by `J` is the categorical
generalization of the subobject `{a ∈ A | ∀ j₁ j₂, f(j₁, a) = f(j₂, a)}`. Note that if `J` has
fewer than two morphisms this condition is trivial, so some lemmas and definitions assume `J` is
nonempty.

## Main definitions

* `walking_parallel_family` is the indexing category used for wide (co)equalizer diagrams
* `parallel_family` is a functor from `walking_parallel_family` to our category `C`.
* a `trident` is a cone over a parallel family.
  * there is really only one interesting morphism in a trident: the arrow from the vertex of the
    trident to the domain of f and g. It is called `trident.ι`.
* a `wide_equalizer` is now just a `limit (parallel_family f)`

Each of these has a dual.

## Main statements

* `wide_equalizer.ι_mono` states that every wide_equalizer map is a monomorphism
* `is_iso_limit_cone_parallel_family_of_self` states that the identity on the domain of `f` is an
  equalizer of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/


noncomputable section

namespace CategoryTheory.Limits

open CategoryTheory

universe w v u u₂

variable {J : Type w}

/-- The type of objects for the diagram indexing a wide (co)equalizer. -/
inductive WalkingParallelFamily (J : Type w) : Type w
  | zero : walking_parallel_family
  | one : walking_parallel_family

open WalkingParallelFamily

instance : DecidableEq (WalkingParallelFamily J)
  | zero, zero => isTrue rfl
  | zero, one => isFalse fun t => WalkingParallelFamily.noConfusion t
  | one, zero => isFalse fun t => WalkingParallelFamily.noConfusion t
  | one, one => isTrue rfl

instance : Inhabited (WalkingParallelFamily J) :=
  ⟨zero⟩

/-- The type family of morphisms for the diagram indexing a wide (co)equalizer. -/
inductive WalkingParallelFamily.Hom (J : Type w) : WalkingParallelFamily J → WalkingParallelFamily J → Type w
  | id : ∀ X : WalkingParallelFamily.{w} J, walking_parallel_family.hom X X
  | line : ∀ j : J, walking_parallel_family.hom zero one
  deriving DecidableEq

/-- Satisfying the inhabited linter -/
instance (J : Type v) : Inhabited (WalkingParallelFamily.Hom J zero zero) where default := Hom.id _

open WalkingParallelFamily.Hom

/-- Composition of morphisms in the indexing diagram for wide (co)equalizers. -/
def WalkingParallelFamily.Hom.comp :
    ∀ (X Y Z : WalkingParallelFamily J) (f : WalkingParallelFamily.Hom J X Y) (g : WalkingParallelFamily.Hom J Y Z),
      WalkingParallelFamily.Hom J X Z
  | _, _, _, id _, h => h
  | _, _, _, line j, id one => line j

attribute [local tidy] tactic.case_bash

instance WalkingParallelFamily.category : SmallCategory (WalkingParallelFamily J) where
  Hom := WalkingParallelFamily.Hom J
  id := WalkingParallelFamily.Hom.id
  comp := WalkingParallelFamily.Hom.comp

@[simp]
theorem WalkingParallelFamily.hom_id (X : WalkingParallelFamily J) : WalkingParallelFamily.Hom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (f : J → (X ⟶ Y))

/-- `parallel_family f` is the diagram in `C` consisting of the given family of morphisms, each with
common domain and codomain.
-/
def parallelFamily : WalkingParallelFamily J ⥤ C where
  obj := fun x => WalkingParallelFamily.casesOn x X Y
  map := fun x y h =>
    match x, y, h with
    | _, _, id _ => 𝟙 _
    | _, _, line j => f j
  map_comp' := by
    rintro _ _ _ ⟨⟩ ⟨⟩ <;>
      · unfold_aux
        simp <;> rfl
        

@[simp]
theorem parallel_family_obj_zero : (parallelFamily f).obj zero = X :=
  rfl

@[simp]
theorem parallel_family_obj_one : (parallelFamily f).obj one = Y :=
  rfl

@[simp]
theorem parallel_family_map_left {j : J} : (parallelFamily f).map (line j) = f j :=
  rfl

/-- Every functor indexing a wide (co)equalizer is naturally isomorphic (actually, equal) to a
    `parallel_family` -/
@[simps]
def diagramIsoParallelFamily (F : WalkingParallelFamily J ⥤ C) : F ≅ parallelFamily fun j => F.map (line j) :=
  (NatIso.ofComponents fun j =>
      eq_to_iso <| by
        cases j <;> tidy) <|
    by
    tidy

/-- `walking_parallel_pair` as a category is equivalent to a special case of
`walking_parallel_family`.  -/
@[simps]
def walkingParallelFamilyEquivWalkingParallelPair : WalkingParallelFamily.{w} (ULift Bool) ≌ walking_parallel_pair where
  Functor := parallelFamily fun p => cond p.down WalkingParallelPairHom.left WalkingParallelPairHom.right
  inverse := parallelPair (line (ULift.up true)) (line (ULift.up false))
  unitIso :=
    NatIso.ofComponents
      (fun X =>
        eqToIso
          (by
            cases X <;> rfl))
      (by
        tidy)
  counitIso :=
    NatIso.ofComponents
      (fun X =>
        eqToIso
          (by
            cases X <;> rfl))
      (by
        tidy)

/-- A trident on `f` is just a `cone (parallel_family f)`. -/
abbrev Trident :=
  Cone (parallelFamily f)

/-- A cotrident on `f` and `g` is just a `cocone (parallel_family f)`. -/
abbrev Cotrident :=
  Cocone (parallelFamily f)

variable {f}

/-- A trident `t` on the parallel family `f : J → (X ⟶ Y)` consists of two morphisms
    `t.π.app zero : t.X ⟶ X` and `t.π.app one : t.X ⟶ Y`. Of these, only the first one is
    interesting, and we give it the shorter name `trident.ι t`. -/
abbrev Trident.ι (t : Trident f) :=
  t.π.app zero

/-- A cotrident `t` on the parallel family `f : J → (X ⟶ Y)` consists of two morphisms
    `t.ι.app zero : X ⟶ t.X` and `t.ι.app one : Y ⟶ t.X`. Of these, only the second one is
    interesting, and we give it the shorter name `cotrident.π t`. -/
abbrev Cotrident.π (t : Cotrident f) :=
  t.ι.app one

@[simp]
theorem Trident.ι_eq_app_zero (t : Trident f) : t.ι = t.π.app zero :=
  rfl

@[simp]
theorem Cotrident.π_eq_app_one (t : Cotrident f) : t.π = t.ι.app one :=
  rfl

@[simp, reassoc]
theorem Trident.app_zero (s : Trident f) (j : J) : s.π.app zero ≫ f j = s.π.app one := by
  rw [← s.w (line j), parallel_family_map_left]

@[simp, reassoc]
theorem Cotrident.app_one (s : Cotrident f) (j : J) : f j ≫ s.ι.app one = s.ι.app zero := by
  rw [← s.w (line j), parallel_family_map_left]

/-- A trident on `f : J → (X ⟶ Y)` is determined by the morphism `ι : P ⟶ X` satisfying
`∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂`.
-/
@[simps]
def Trident.ofι [Nonempty J] {P : C} (ι : P ⟶ X) (w : ∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂) : Trident f where
  x := P
  π :=
    { app := fun X => WalkingParallelFamily.casesOn X ι (ι ≫ f (Classical.arbitrary J)),
      naturality' := fun i j f => by
        dsimp'
        cases' f with _ k
        · simp
          
        · simp [← w (Classical.arbitrary J) k]
           }

/-- A cotrident on `f : J → (X ⟶ Y)` is determined by the morphism `π : Y ⟶ P` satisfying
`∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π`.
-/
@[simps]
def Cotrident.ofπ [Nonempty J] {P : C} (π : Y ⟶ P) (w : ∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π) : Cotrident f where
  x := P
  ι :=
    { app := fun X => WalkingParallelFamily.casesOn X (f (Classical.arbitrary J) ≫ π) π,
      naturality' := fun i j f => by
        dsimp'
        cases' f with _ k
        · simp
          
        · simp [← w (Classical.arbitrary J) k]
           }

-- See note [dsimp, simp]
theorem Trident.ι_of_ι [Nonempty J] {P : C} (ι : P ⟶ X) (w : ∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂) : (Trident.ofι ι w).ι = ι :=
  rfl

theorem Cotrident.π_of_π [Nonempty J] {P : C} (π : Y ⟶ P) (w : ∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π) :
    (Cotrident.ofπ π w).π = π :=
  rfl

@[reassoc]
theorem Trident.condition (j₁ j₂ : J) (t : Trident f) : t.ι ≫ f j₁ = t.ι ≫ f j₂ := by
  rw [t.app_zero, t.app_zero]

@[reassoc]
theorem Cotrident.condition (j₁ j₂ : J) (t : Cotrident f) : f j₁ ≫ t.π = f j₂ ≫ t.π := by
  rw [t.app_one, t.app_one]

/-- To check whether two maps are equalized by both maps of a trident, it suffices to check it for
the first map -/
theorem Trident.equalizer_ext [Nonempty J] (s : Trident f) {W : C} {k l : W ⟶ s.x} (h : k ≫ s.ι = l ≫ s.ι) :
    ∀ j : WalkingParallelFamily J, k ≫ s.π.app j = l ≫ s.π.app j
  | zero => h
  | one => by
    rw [← s.app_zero (Classical.arbitrary J), reassoc_of h]

/-- To check whether two maps are coequalized by both maps of a cotrident, it suffices to check it
for the second map -/
theorem Cotrident.coequalizer_ext [Nonempty J] (s : Cotrident f) {W : C} {k l : s.x ⟶ W} (h : s.π ≫ k = s.π ≫ l) :
    ∀ j : WalkingParallelFamily J, s.ι.app j ≫ k = s.ι.app j ≫ l
  | zero => by
    rw [← s.app_one (Classical.arbitrary J), category.assoc, category.assoc, h]
  | one => h

theorem Trident.IsLimit.hom_ext [Nonempty J] {s : Trident f} (hs : IsLimit s) {W : C} {k l : W ⟶ s.x}
    (h : k ≫ s.ι = l ≫ s.ι) : k = l :=
  hs.hom_ext <| Trident.equalizer_ext _ h

theorem Cotrident.IsColimit.hom_ext [Nonempty J] {s : Cotrident f} (hs : IsColimit s) {W : C} {k l : s.x ⟶ W}
    (h : s.π ≫ k = s.π ≫ l) : k = l :=
  hs.hom_ext <| Cotrident.coequalizer_ext _ h

/-- If `s` is a limit trident over `f`, then a morphism `k : W ⟶ X` satisfying
    `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` induces a morphism `l : W ⟶ s.X` such that
    `l ≫ trident.ι s = k`. -/
def Trident.IsLimit.lift' [Nonempty J] {s : Trident f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) : { l : W ⟶ s.x // l ≫ Trident.ι s = k } :=
  ⟨hs.lift <| Trident.ofι _ h, hs.fac _ _⟩

/-- If `s` is a colimit cotrident over `f`, then a morphism `k : Y ⟶ W` satisfying
    `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` induces a morphism `l : s.X ⟶ W` such that
    `cotrident.π s ≫ l = k`. -/
def Cotrident.IsColimit.desc' [Nonempty J] {s : Cotrident f} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) : { l : s.x ⟶ W // Cotrident.π s ≫ l = k } :=
  ⟨hs.desc <| Cotrident.ofπ _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a trident is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
def Trident.IsLimit.mk [Nonempty J] (t : Trident f) (lift : ∀ s : Trident f, s.x ⟶ t.x)
    (fac : ∀ s : Trident f, lift s ≫ t.ι = s.ι)
    (uniq :
      ∀ (s : Trident f) (m : s.x ⟶ t.x) (w : ∀ j : WalkingParallelFamily J, m ≫ t.π.app j = s.π.app j), m = lift s) :
    IsLimit t :=
  { lift,
    fac' := fun s j =>
      WalkingParallelFamily.casesOn j (fac s)
        (by
          rw [← t.w (line (Classical.arbitrary J)), reassoc_of fac, s.w]),
    uniq' := uniq }

/-- This is another convenient method to verify that a trident is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def Trident.IsLimit.mk' [Nonempty J] (t : Trident f)
    (create : ∀ s : Trident f, { l // l ≫ t.ι = s.ι ∧ ∀ {m}, m ≫ t.ι = s.ι → m = l }) : IsLimit t :=
  Trident.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s m w => (create s).2.2 (w zero)

/-- This is a slightly more convenient method to verify that a cotrident is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content -/
def Cotrident.IsColimit.mk [Nonempty J] (t : Cotrident f) (desc : ∀ s : Cotrident f, t.x ⟶ s.x)
    (fac : ∀ s : Cotrident f, t.π ≫ desc s = s.π)
    (uniq :
      ∀ (s : Cotrident f) (m : t.x ⟶ s.x) (w : ∀ j : WalkingParallelFamily J, t.ι.app j ≫ m = s.ι.app j), m = desc s) :
    IsColimit t :=
  { desc,
    fac' := fun s j =>
      WalkingParallelFamily.casesOn j
        (by
          rw [← t.w_assoc (line (Classical.arbitrary J)), fac, s.w])
        (fac s),
    uniq' := uniq }

/-- This is another convenient method to verify that a cotrident is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
def Cotrident.IsColimit.mk' [Nonempty J] (t : Cotrident f)
    (create : ∀ s : Cotrident f, { l : t.x ⟶ s.x // t.π ≫ l = s.π ∧ ∀ {m}, t.π ≫ m = s.π → m = l }) : IsColimit t :=
  Cotrident.IsColimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s m w => (create s).2.2 (w one)

/-- Given a limit cone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms from `Z` to its point
are in bijection with morphisms `h : Z ⟶ X` such that `∀ j₁ j₂, h ≫ f j₁ = h ≫ f j₂`.
Further, this bijection is natural in `Z`: see `trident.is_limit.hom_iso_natural`.
-/
@[simps]
def Trident.IsLimit.homIso [Nonempty J] {t : Trident f} (ht : IsLimit t) (Z : C) :
    (Z ⟶ t.x) ≃ { h : Z ⟶ X // ∀ j₁ j₂, h ≫ f j₁ = h ≫ f j₂ } where
  toFun := fun k =>
    ⟨k ≫ t.ι, by
      simp ⟩
  invFun := fun h => (Trident.IsLimit.lift' ht _ h.Prop).1
  left_inv := fun k => Trident.IsLimit.hom_ext ht (Trident.IsLimit.lift' _ _ _).Prop
  right_inv := fun h => Subtype.ext (Trident.IsLimit.lift' ht _ _).Prop

/-- The bijection of `trident.is_limit.hom_iso` is natural in `Z`. -/
theorem Trident.IsLimit.hom_iso_natural [Nonempty J] {t : Trident f} (ht : IsLimit t) {Z Z' : C} (q : Z' ⟶ Z)
    (k : Z ⟶ t.x) : (Trident.IsLimit.homIso ht _ (q ≫ k) : Z' ⟶ X) = q ≫ (Trident.IsLimit.homIso ht _ k : Z ⟶ X) :=
  Category.assoc _ _ _

/-- Given a colimit cocone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms from the cocone
point to `Z` are in bijection with morphisms `h : Z ⟶ X` such that
`∀ j₁ j₂, f j₁ ≫ h = f j₂ ≫ h`.  Further, this bijection is natural in `Z`: see
`cotrident.is_colimit.hom_iso_natural`.
-/
@[simps]
def Cotrident.IsColimit.homIso [Nonempty J] {t : Cotrident f} (ht : IsColimit t) (Z : C) :
    (t.x ⟶ Z) ≃ { h : Y ⟶ Z // ∀ j₁ j₂, f j₁ ≫ h = f j₂ ≫ h } where
  toFun := fun k =>
    ⟨t.π ≫ k, by
      simp ⟩
  invFun := fun h => (Cotrident.IsColimit.desc' ht _ h.Prop).1
  left_inv := fun k => Cotrident.IsColimit.hom_ext ht (Cotrident.IsColimit.desc' _ _ _).Prop
  right_inv := fun h => Subtype.ext (Cotrident.IsColimit.desc' ht _ _).Prop

/-- The bijection of `cotrident.is_colimit.hom_iso` is natural in `Z`. -/
theorem Cotrident.IsColimit.hom_iso_natural [Nonempty J] {t : Cotrident f} {Z Z' : C} (q : Z ⟶ Z') (ht : IsColimit t)
    (k : t.x ⟶ Z) :
    (Cotrident.IsColimit.homIso ht _ (k ≫ q) : Y ⟶ Z') = (Cotrident.IsColimit.homIso ht _ k : Y ⟶ Z) ≫ q :=
  (Category.assoc _ _ _).symm

/-- This is a helper construction that can be useful when verifying that a category has certain wide
    equalizers. Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (λ j, F.map (line j))`, and a trident on `λ j, F.map (line j)`, we get a cone
    on `F`.

    If you're thinking about using this, have a look at
    `has_wide_equalizers_of_has_limit_parallel_family`, which you may find to be an easier way of
    achieving your goal. -/
def Cone.ofTrident {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j)) : Cone F where
  x := t.x
  π :=
    { app := fun X =>
        t.π.app X ≫
          eqToHom
            (by
              tidy),
      naturality' := fun j j' g => by
        cases g <;>
          · dsimp'
            simp
             }

/-- This is a helper construction that can be useful when verifying that a category has all
    coequalizers. Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (λ j, F.map (line j))`, and a cotrident on `λ j, F.map (line j)` we get a
    cocone on `F`.

    If you're thinking about using this, have a look at
    `has_wide_coequalizers_of_has_colimit_parallel_family`, which you may find to be an easier way
    of achieving your goal. -/
def Cocone.ofCotrident {F : WalkingParallelFamily J ⥤ C} (t : Cotrident fun j => F.map (line j)) : Cocone F where
  x := t.x
  ι :=
    { app := fun X =>
        eqToHom
            (by
              tidy) ≫
          t.ι.app X,
      naturality' := fun j j' g => by
        cases g <;> dsimp' <;> simp [← cotrident.app_one t] }

@[simp]
theorem Cone.of_trident_π {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j)) (j) :
    (Cone.ofTrident t).π.app j =
      t.π.app j ≫
        eqToHom
          (by
            tidy) :=
  rfl

@[simp]
theorem Cocone.of_cotrident_ι {F : WalkingParallelFamily J ⥤ C} (t : Cotrident fun j => F.map (line j)) (j) :
    (Cocone.ofCotrident t).ι.app j =
      eqToHom
          (by
            tidy) ≫
        t.ι.app j :=
  rfl

/-- Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (λ j, F.map (line j))` and a cone on `F`, we get a trident on
    `λ j, F.map (line j)`. -/
def Trident.ofCone {F : WalkingParallelFamily J ⥤ C} (t : Cone F) : Trident fun j => F.map (line j) where
  x := t.x
  π :=
    { app := fun X =>
        t.π.app X ≫
          eqToHom
            (by
              tidy) }

/-- Given `F : walking_parallel_family ⥤ C`, which is really the same as
    `parallel_family (F.map left) (F.map right)` and a cocone on `F`, we get a cotrident on
    `λ j, F.map (line j)`. -/
def Cotrident.ofCocone {F : WalkingParallelFamily J ⥤ C} (t : Cocone F) : Cotrident fun j => F.map (line j) where
  x := t.x
  ι :=
    { app := fun X =>
        eqToHom
            (by
              tidy) ≫
          t.ι.app X }

@[simp]
theorem Trident.of_cone_π {F : WalkingParallelFamily J ⥤ C} (t : Cone F) (j) :
    (Trident.ofCone t).π.app j =
      t.π.app j ≫
        eqToHom
          (by
            tidy) :=
  rfl

@[simp]
theorem Cotrident.of_cocone_ι {F : WalkingParallelFamily J ⥤ C} (t : Cocone F) (j) :
    (Cotrident.ofCocone t).ι.app j =
      eqToHom
          (by
            tidy) ≫
        t.ι.app j :=
  rfl

/-- Helper function for constructing morphisms between wide equalizer tridents.
-/
@[simps]
def Trident.mkHom [Nonempty J] {s t : Trident f} (k : s.x ⟶ t.x) (w : k ≫ t.ι = s.ι) : s ⟶ t where
  Hom := k
  w' := by
    rintro ⟨_ | _⟩
    · exact w
      
    · simpa using w =≫ f (Classical.arbitrary J)
      

/-- To construct an isomorphism between tridents,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simps]
def Trident.ext [Nonempty J] {s t : Trident f} (i : s.x ≅ t.x) (w : i.Hom ≫ t.ι = s.ι) : s ≅ t where
  Hom := Trident.mkHom i.Hom w
  inv :=
    Trident.mkHom i.inv
      (by
        rw [← w, iso.inv_hom_id_assoc])

/-- Helper function for constructing morphisms between coequalizer cotridents.
-/
@[simps]
def Cotrident.mkHom [Nonempty J] {s t : Cotrident f} (k : s.x ⟶ t.x) (w : s.π ≫ k = t.π) : s ⟶ t where
  Hom := k
  w' := by
    rintro ⟨_ | _⟩
    · simpa using f (Classical.arbitrary J) ≫= w
      
    · exact w
      

/-- To construct an isomorphism between cotridents,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
def Cotrident.ext [Nonempty J] {s t : Cotrident f} (i : s.x ≅ t.x) (w : s.π ≫ i.Hom = t.π) : s ≅ t where
  Hom := Cotrident.mkHom i.Hom w
  inv :=
    Cotrident.mkHom i.inv
      (by
        rw [iso.comp_inv_eq, w])

variable (f)

section

/-- `has_wide_equalizer f` represents a particular choice of limiting cone for the parallel family of
morphisms `f`.
-/
abbrev HasWideEqualizer :=
  HasLimit (parallelFamily f)

variable [HasWideEqualizer f]

/-- If a wide equalizer of `f` exists, we can access an arbitrary choice of such by
    saying `wide_equalizer f`. -/
abbrev wideEqualizer : C :=
  limit (parallelFamily f)

/-- If a wide equalizer of `f` exists, we can access the inclusion `wide_equalizer f ⟶ X` by
    saying `wide_equalizer.ι f`. -/
abbrev wideEqualizer.ι : wideEqualizer f ⟶ X :=
  limit.π (parallelFamily f) zero

/-- A wide equalizer cone for a parallel family `f`.
-/
abbrev wideEqualizer.trident : Trident f :=
  Limit.cone (parallelFamily f)

@[simp]
theorem wideEqualizer.trident_ι : (wideEqualizer.trident f).ι = wideEqualizer.ι f :=
  rfl

@[simp]
theorem wideEqualizer.trident_π_app_zero : (wideEqualizer.trident f).π.app zero = wideEqualizer.ι f :=
  rfl

@[reassoc]
theorem wideEqualizer.condition (j₁ j₂ : J) : wideEqualizer.ι f ≫ f j₁ = wideEqualizer.ι f ≫ f j₂ :=
  Trident.condition j₁ j₂ <| limit.cone <| parallelFamily f

/-- The wide_equalizer built from `wide_equalizer.ι f` is limiting. -/
def wideEqualizerIsWideEqualizer [Nonempty J] : IsLimit (Trident.ofι (wideEqualizer.ι f) (wideEqualizer.condition f)) :=
  IsLimit.ofIsoLimit (limit.isLimit _)
    (Trident.ext (Iso.refl _)
      (by
        tidy))

variable {f}

/-- A morphism `k : W ⟶ X` satisfying `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` factors through the
    wide equalizer of `f` via `wide_equalizer.lift : W ⟶ wide_equalizer f`. -/
abbrev wideEqualizer.lift [Nonempty J] {W : C} (k : W ⟶ X) (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) : W ⟶ wideEqualizer f :=
  limit.lift (parallelFamily f) (Trident.ofι k h)

@[simp, reassoc]
theorem wideEqualizer.lift_ι [Nonempty J] {W : C} (k : W ⟶ X) (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    wideEqualizer.lift k h ≫ wideEqualizer.ι f = k :=
  limit.lift_π _ _

/-- A morphism `k : W ⟶ X` satisfying `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` induces a morphism
    `l : W ⟶ wide_equalizer f` satisfying `l ≫ wide_equalizer.ι f = k`. -/
def wideEqualizer.lift' [Nonempty J] {W : C} (k : W ⟶ X) (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    { l : W ⟶ wideEqualizer f // l ≫ wideEqualizer.ι f = k } :=
  ⟨wideEqualizer.lift k h, wideEqualizer.lift_ι _ _⟩

/-- Two maps into a wide equalizer are equal if they are are equal when composed with the wide
    equalizer map. -/
@[ext]
theorem wideEqualizer.hom_ext [Nonempty J] {W : C} {k l : W ⟶ wideEqualizer f}
    (h : k ≫ wideEqualizer.ι f = l ≫ wideEqualizer.ι f) : k = l :=
  Trident.IsLimit.hom_ext (limit.isLimit _) h

/-- A wide equalizer morphism is a monomorphism -/
instance wideEqualizer.ι_mono [Nonempty J] :
    Mono (wideEqualizer.ι f) where right_cancellation := fun Z h k w => wideEqualizer.hom_ext w

end

section

variable {f}

/-- The wide equalizer morphism in any limit cone is a monomorphism. -/
theorem mono_of_is_limit_parallel_family [Nonempty J] {c : Cone (parallelFamily f)} (i : IsLimit c) :
    Mono (Trident.ι c) :=
  { right_cancellation := fun Z h k w => Trident.IsLimit.hom_ext i w }

end

section

/-- `has_wide_coequalizer f g` represents a particular choice of colimiting cocone
for the parallel family of morphisms `f`.
-/
abbrev HasWideCoequalizer :=
  HasColimit (parallelFamily f)

variable [HasWideCoequalizer f]

/-- If a wide coequalizer of `f`, we can access an arbitrary choice of such by
    saying `wide_coequalizer f`. -/
abbrev wideCoequalizer : C :=
  colimit (parallelFamily f)

/-- If a wide_coequalizer of `f` exists, we can access the corresponding projection by
    saying `wide_coequalizer.π f`. -/
abbrev wideCoequalizer.π : Y ⟶ wideCoequalizer f :=
  colimit.ι (parallelFamily f) one

/-- An arbitrary choice of coequalizer cocone for a parallel family `f`.
-/
abbrev wideCoequalizer.cotrident : Cotrident f :=
  Colimit.cocone (parallelFamily f)

@[simp]
theorem wideCoequalizer.cotrident_π : (wideCoequalizer.cotrident f).π = wideCoequalizer.π f :=
  rfl

@[simp]
theorem wideCoequalizer.cotrident_ι_app_one : (wideCoequalizer.cotrident f).ι.app one = wideCoequalizer.π f :=
  rfl

@[reassoc]
theorem wideCoequalizer.condition (j₁ j₂ : J) : f j₁ ≫ wideCoequalizer.π f = f j₂ ≫ wideCoequalizer.π f :=
  Cotrident.condition j₁ j₂ <| colimit.cocone <| parallelFamily f

/-- The cotrident built from `wide_coequalizer.π f` is colimiting. -/
def wideCoequalizerIsWideCoequalizer [Nonempty J] :
    IsColimit (Cotrident.ofπ (wideCoequalizer.π f) (wideCoequalizer.condition f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cotrident.ext (Iso.refl _)
      (by
        tidy))

variable {f}

/-- Any morphism `k : Y ⟶ W` satisfying `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` factors through the
    wide coequalizer of `f` via `wide_coequalizer.desc : wide_coequalizer f ⟶ W`. -/
abbrev wideCoequalizer.desc [Nonempty J] {W : C} (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    wideCoequalizer f ⟶ W :=
  colimit.desc (parallelFamily f) (Cotrident.ofπ k h)

@[simp, reassoc]
theorem wideCoequalizer.π_desc [Nonempty J] {W : C} (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    wideCoequalizer.π f ≫ wideCoequalizer.desc k h = k :=
  colimit.ι_desc _ _

/-- Any morphism `k : Y ⟶ W` satisfying `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` induces a morphism
    `l : wide_coequalizer f ⟶ W` satisfying `wide_coequalizer.π ≫ g = l`. -/
def wideCoequalizer.desc' [Nonempty J] {W : C} (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    { l : wideCoequalizer f ⟶ W // wideCoequalizer.π f ≫ l = k } :=
  ⟨wideCoequalizer.desc k h, wideCoequalizer.π_desc _ _⟩

/-- Two maps from a wide coequalizer are equal if they are equal when composed with the wide
    coequalizer map -/
@[ext]
theorem wideCoequalizer.hom_ext [Nonempty J] {W : C} {k l : wideCoequalizer f ⟶ W}
    (h : wideCoequalizer.π f ≫ k = wideCoequalizer.π f ≫ l) : k = l :=
  Cotrident.IsColimit.hom_ext (colimit.isColimit _) h

/-- A wide coequalizer morphism is an epimorphism -/
instance wideCoequalizer.π_epi [Nonempty J] :
    Epi (wideCoequalizer.π f) where left_cancellation := fun Z h k w => wideCoequalizer.hom_ext w

end

section

variable {f}

/-- The wide coequalizer morphism in any colimit cocone is an epimorphism. -/
theorem epi_of_is_colimit_parallel_family [Nonempty J] {c : Cocone (parallelFamily f)} (i : IsColimit c) :
    Epi (c.ι.app one) :=
  { left_cancellation := fun Z h k w => Cotrident.IsColimit.hom_ext i w }

end

variable (C)

/-- `has_wide_equalizers` represents a choice of wide equalizer for every family of morphisms -/
abbrev HasWideEqualizers :=
  ∀ J, HasLimitsOfShape (WalkingParallelFamily.{w} J) C

/-- `has_wide_coequalizers` represents a choice of wide coequalizer for every family of morphisms -/
abbrev HasWideCoequalizers :=
  ∀ J, HasColimitsOfShape (WalkingParallelFamily.{w} J) C

/-- If `C` has all limits of diagrams `parallel_family f`, then it has all wide equalizers -/
theorem has_wide_equalizers_of_has_limit_parallel_family
    [∀ {J : Type w} {X Y : C} {f : J → (X ⟶ Y)}, HasLimit (parallelFamily f)] : HasWideEqualizers.{w} C := fun J =>
  { HasLimit := fun F => has_limit_of_iso (diagramIsoParallelFamily F).symm }

/-- If `C` has all colimits of diagrams `parallel_family f`, then it has all wide coequalizers -/
theorem has_wide_coequalizers_of_has_colimit_parallel_family
    [∀ {J : Type w} {X Y : C} {f : J → (X ⟶ Y)}, HasColimit (parallelFamily f)] : HasWideCoequalizers.{w} C := fun J =>
  { HasColimit := fun F => has_colimit_of_iso (diagramIsoParallelFamily F) }

instance (priority := 10) has_equalizers_of_has_wide_equalizers [HasWideEqualizers.{w} C] : HasEqualizers C :=
  has_limits_of_shape_of_equivalence.{w} walkingParallelFamilyEquivWalkingParallelPair

instance (priority := 10) has_coequalizers_of_has_wide_coequalizers [HasWideCoequalizers.{w} C] : HasCoequalizers C :=
  has_colimits_of_shape_of_equivalence.{w} walkingParallelFamilyEquivWalkingParallelPair

end CategoryTheory.Limits

