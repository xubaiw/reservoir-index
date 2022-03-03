/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.CategoryTheory.Limits.Types
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!
# Special shapes for limits in `Type`.

The general shape (co)limits defined in `category_theory.limits.types`
are intended for use through the limits API,
and the actual implementation should mostly be considered "sealed".

In this file, we provide definitions of the "standard" special shapes of limits in `Type`,
giving the expected definitional implementation:
* the terminal object is `punit`
* the binary product of `X` and `Y` is `X × Y`
* the product of a family `f : J → Type` is `Π j, f j`
* the coproduct of a family `f : J → Type` is `Σ j, f j`
* the binary coproduct of `X` and `Y` is the sum type `X ⊕ Y`
* the equalizer of a pair of maps `(g, h)` is the subtype `{x : Y // g x = h x}`
* the coequalizer of a pair of maps `(f, g)` is the quotient of `Y` by `∀ x : Y, f x ~ g x`
* the pullback of `f : X ⟶ Z` and `g : Y ⟶ Z` is the subtype `{ p : X × Y // f p.1 = g p.2 }`
  of the product

Because these are not intended for use with the `has_limit` API,
we instead construct terms of `limit_data`.

As an example, when setting up the monoidal category structure on `Type`
we use the `types_has_terminal` and `types_has_binary_products` instances.
-/


universe u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Limits.Types

/-- A restatement of `types.lift_π_apply` that uses `pi.π` and `pi.lift`. -/
@[simp]
theorem pi_lift_π_apply {β : Type u} (f : β → Type u) {P : Type u} (s : ∀ b, P ⟶ f b) (b : β) (x : P) :
    (Pi.π f b : (∏ f) → f b) (@Pi.lift β _ _ f _ P s x) = s b x :=
  congr_funₓ (limit.lift_π (Fan.mk P s) b) x

/-- A restatement of `types.map_π_apply` that uses `pi.π` and `pi.map`. -/
@[simp]
theorem pi_map_π_apply {β : Type u} {f g : β → Type u} (α : ∀ j, f j ⟶ g j) (b : β) x :
    (Pi.π g b : (∏ g) → g b) (Pi.map α x) = α b ((Pi.π f b : (∏ f) → f b) x) :=
  Limit.map_π_apply _ _ _

/-- The category of types has `punit` as a terminal object. -/
def terminalLimitCone : Limits.LimitCone (Functor.empty (Type u)) where
  Cone :=
    { x := PUnit,
      π := by
        tidy }
  IsLimit := by
    tidy

/-- The category of types has `pempty` as an initial object. -/
def initialLimitCone : Limits.ColimitCocone (Functor.empty (Type u)) where
  Cocone :=
    { x := Pempty,
      ι := by
        tidy }
  IsColimit := by
    tidy

open CategoryTheory.Limits.WalkingPair

/-- The product type `X × Y` forms a cone for the binary product of `X` and `Y`. -/
-- We manually generate the other projection lemmas since the simp-normal form for the legs is
-- otherwise not created correctly.
@[simps x]
def binaryProductCone (X Y : Type u) : BinaryFan X Y :=
  BinaryFan.mk Prod.fst Prod.snd

@[simp]
theorem binary_product_cone_fst (X Y : Type u) : (binaryProductCone X Y).fst = Prod.fst :=
  rfl

@[simp]
theorem binary_product_cone_snd (X Y : Type u) : (binaryProductCone X Y).snd = Prod.snd :=
  rfl

/-- The product type `X × Y` is a binary product for `X` and `Y`. -/
@[simps]
def binaryProductLimit (X Y : Type u) : IsLimit (binaryProductCone X Y) where
  lift := fun x => (s.fst x, s.snd x)
  fac' := fun s j => WalkingPair.casesOn j rfl rfl
  uniq' := fun s m w => funext fun x => Prod.extₓ (congr_funₓ (w left) x) (congr_funₓ (w right) x)

/-- The category of types has `X × Y`, the usual cartesian product,
as the binary product of `X` and `Y`.
-/
@[simps]
def binaryProductLimitCone (X Y : Type u) : Limits.LimitCone (pair X Y) :=
  ⟨_, binaryProductLimit X Y⟩

/-- The functor which sends `X, Y` to the product type `X × Y`. -/
-- We add the option `type_md` to tell `@[simps]` to not treat homomorphisms `X ⟶ Y` in `Type*` as
-- a function type
@[simps (config := { typeMd := reducible })]
def binaryProductFunctor : Type u ⥤ Type u ⥤ Type u where
  obj := fun X =>
    { obj := fun Y => X × Y,
      map := fun Y₁ Y₂ f => (binaryProductLimit X Y₂).lift (BinaryFan.mk Prod.fst (Prod.snd ≫ f)) }
  map := fun X₁ X₂ f => { app := fun Y => (binaryProductLimit X₂ Y).lift (BinaryFan.mk (Prod.fst ≫ f) Prod.snd) }

/-- The product functor given by the instance `has_binary_products (Type u)` is isomorphic to the
explicit binary product functor given by the product type.
-/
noncomputable def binaryProductIsoProd : binary_product_functor ≅ (prod.functor : Type u ⥤ _) := by
  apply nat_iso.of_components (fun X => _) _
  · apply nat_iso.of_components (fun Y => _) _
    · exact ((limit.is_limit _).conePointUniqueUpToIso (binary_product_limit X Y)).symm
      
    · intro Y₁ Y₂ f
      ext1 <;> simp
      
    
  · intro X₁ X₂ g
    ext : 3 <;> simp
    

/-- The sum type `X ⊕ Y` forms a cocone for the binary coproduct of `X` and `Y`. -/
@[simps]
def binaryCoproductCocone (X Y : Type u) : Cocone (pair X Y) :=
  BinaryCofan.mk Sum.inl Sum.inr

/-- The sum type `X ⊕ Y` is a binary coproduct for `X` and `Y`. -/
@[simps]
def binaryCoproductColimit (X Y : Type u) : IsColimit (binaryCoproductCocone X Y) where
  desc := fun s : BinaryCofan X Y => Sum.elim s.inl s.inr
  fac' := fun s j => WalkingPair.casesOn j rfl rfl
  uniq' := fun s m w => funext fun x => Sum.casesOn x (congr_funₓ (w left)) (congr_funₓ (w right))

/-- The category of types has `X ⊕ Y`,
as the binary coproduct of `X` and `Y`.
-/
def binaryCoproductColimitCocone (X Y : Type u) : Limits.ColimitCocone (pair X Y) :=
  ⟨_, binaryCoproductColimit X Y⟩

/-- The category of types has `Π j, f j` as the product of a type family `f : J → Type`.
-/
def productLimitCone {J : Type u} (F : J → Type u) : Limits.LimitCone (Discrete.functor F) where
  Cone := { x := ∀ j, F j, π := { app := fun j f => f j } }
  IsLimit :=
    { lift := fun s x j => s.π.app j x, uniq' := fun s m w => funext fun x => funext fun j => (congr_funₓ (w j) x : _) }

/-- The category of types has `Σ j, f j` as the coproduct of a type family `f : J → Type`.
-/
def coproductColimitCocone {J : Type u} (F : J → Type u) : Limits.ColimitCocone (Discrete.functor F) where
  Cocone := { x := Σj, F j, ι := { app := fun j x => ⟨j, x⟩ } }
  IsColimit :=
    { desc := fun s x => s.ι.app x.1 x.2,
      uniq' := fun s m w => by
        ext ⟨j, x⟩
        have := congr_funₓ (w j) x
        exact this }

section Fork

variable {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)

/-- Show the given fork in `Type u` is an equalizer given that any element in the "difference kernel"
comes from `X`.
The converse of `unique_of_type_equalizer`.
-/
noncomputable def typeEqualizerOfUnique (t : ∀ y : Y, g y = h y → ∃! x : X, f x = y) : IsLimit (Fork.ofι _ w) :=
  (Fork.IsLimit.mk' _) fun s => by
    refine' ⟨fun i => _, _, _⟩
    · apply Classical.some (t (s.ι i) _)
      apply congr_funₓ s.condition i
      
    · ext i
      apply (Classical.some_spec (t (s.ι i) _)).1
      
    · intro m hm
      ext i
      apply (Classical.some_spec (t (s.ι i) _)).2
      apply congr_funₓ hm i
      

/-- The converse of `type_equalizer_of_unique`. -/
theorem unique_of_type_equalizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y) : ∃! x : X, f x = y := by
  let y' : PUnit ⟶ Y := fun _ => y
  have hy' : y' ≫ g = y' ≫ h := funext fun _ => hy
  refine' ⟨(fork.is_limit.lift' t _ hy').1 ⟨⟩, congr_funₓ (fork.is_limit.lift' t y' _).2 ⟨⟩, _⟩
  intro x' hx'
  suffices : (fun _ : PUnit => x') = (fork.is_limit.lift' t y' hy').1
  rw [← this]
  apply fork.is_limit.hom_ext t
  ext ⟨⟩
  apply hx'.trans (congr_funₓ (fork.is_limit.lift' t _ hy').2 ⟨⟩).symm

theorem type_equalizer_iff_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ ∀ y : Y, g y = h y → ∃! x : X, f x = y :=
  ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k => ⟨typeEqualizerOfUnique f w k⟩⟩

/-- Show that the subtype `{x : Y // g x = h x}` is an equalizer for the pair `(g,h)`. -/
def equalizerLimit : Limits.LimitCone (parallelPair g h) where
  Cone := Fork.ofι (Subtype.val : { x : Y // g x = h x } → Y) (funext Subtype.prop)
  IsLimit :=
    (Fork.IsLimit.mk' _) fun s =>
      ⟨fun i =>
        ⟨s.ι i, by
          apply congr_funₓ s.condition i⟩,
        rfl, fun m hm => funext fun x => Subtype.ext (congr_funₓ hm x)⟩

end Fork

section Cofork

variable {X Y Z : Type u} (f g : X ⟶ Y)

/-- (Implementation) The relation to be quotiented to obtain the coequalizer. -/
inductive CoequalizerRel : Y → Y → Prop
  | rel (x : X) : coequalizer_rel (f x) (g x)

/-- Show that the quotient by the relation generated by `f(x) ~ g(x)`
is a coequalizer for the pair `(f, g)`.
-/
def coequalizerColimit : Limits.ColimitCocone (parallelPair f g) where
  Cocone := Cofork.ofπ (Quot.mk (CoequalizerRel f g)) (funext fun x => Quot.sound (CoequalizerRel.rel x))
  IsColimit :=
    (Cofork.IsColimit.mk' _) fun s =>
      ⟨Quot.lift s.π fun h : CoequalizerRel f g a b => by
          cases h
          exact congr_funₓ s.condition h_1,
        rfl, fun m hm => funext fun x => Quot.induction_on x (congr_funₓ hm : _)⟩

/-- If `π : Y ⟶ Z` is an equalizer for `(f, g)`, and `U ⊆ Y` such that `f ⁻¹' U = g ⁻¹' U`,
then `π ⁻¹' (π '' U) = U`.
-/
theorem coequalizer_preimage_image_eq_of_preimage_eq (π : Y ⟶ Z) (e : f ≫ π = g ≫ π) (h : IsColimit (Cofork.ofπ π e))
    (U : Set Y) (H : f ⁻¹' U = g ⁻¹' U) : π ⁻¹' (π '' U) = U := by
  have lem : ∀ x y, coequalizer_rel f g x y → (x ∈ U ↔ y ∈ U) := by
    rintro _ _ ⟨x⟩
    change x ∈ f ⁻¹' U ↔ x ∈ g ⁻¹' U
    congr 2
  have eqv : _root_.equivalence fun x y => x ∈ U ↔ y ∈ U := by
    tidy
  ext
  constructor
  · rw [←
      show _ = π from h.comp_cocone_point_unique_up_to_iso_inv (coequalizer_colimit f g).2 walking_parallel_pair.one]
    rintro ⟨y, hy, e'⟩
    dsimp  at e'
    replace e' :=
      (mono_iff_injective (h.cocone_point_unique_up_to_iso (coequalizer_colimit f g).IsColimit).inv).mp inferInstance e'
    exact (eqv.eqv_gen_iff.mp (EqvGen.mono lem (Quot.exact _ e'))).mp hy
    
  · exact fun hx => ⟨x, hx, rfl⟩
    

end Cofork

section Pullback

open CategoryTheory.Limits.WalkingPair

open CategoryTheory.Limits.WalkingCospan

open CategoryTheory.Limits.WalkingCospan.Hom

variable {W X Y Z : Type u}

variable (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The usual explicit pullback in the category of types, as a subtype of the product.
The full `limit_cone` data is bundled as `pullback_limit_cone f g`.
-/
@[nolint has_inhabited_instance]
abbrev PullbackObj : Type u :=
  { p : X × Y // f p.1 = g p.2 }

-- `pullback_obj f g` comes with a coercion to the product type `X × Y`.
example (p : PullbackObj f g) : X × Y :=
  p

/-- The explicit pullback cone on `pullback_obj f g`.
This is bundled with the `is_limit` data as `pullback_limit_cone f g`.
-/
abbrev pullbackCone : Limits.PullbackCone f g :=
  PullbackCone.mk (fun p : PullbackObj f g => p.1.1) (fun p => p.1.2) (funext fun p => p.2)

/-- The explicit pullback in the category of types, bundled up as a `limit_cone`
for given `f` and `g`.
-/
@[simps]
def pullbackLimitCone (f : X ⟶ Z) (g : Y ⟶ Z) : Limits.LimitCone (cospan f g) where
  Cone := pullbackCone f g
  IsLimit :=
    PullbackCone.isLimitAux _ (fun s x => ⟨⟨s.fst x, s.snd x⟩, congr_funₓ s.condition x⟩)
      (by
        tidy)
      (by
        tidy)
      fun s m w =>
      funext fun x =>
        Subtype.ext <| Prod.extₓ (congr_funₓ (w WalkingCospan.left) x) (congr_funₓ (w WalkingCospan.right) x)

/-- The pullback cone given by the instance `has_pullbacks (Type u)` is isomorphic to the
explicit pullback cone given by `pullback_limit_cone`.
-/
noncomputable def pullbackConeIsoPullback : Limit.cone (cospan f g) ≅ pullbackCone f g :=
  (limit.isLimit _).uniqueUpToIso (pullbackLimitCone f g).IsLimit

/-- The pullback given by the instance `has_pullbacks (Type u)` is isomorphic to the
explicit pullback object given by `pullback_limit_obj`.
-/
noncomputable def pullbackIsoPullback : pullback f g ≅ PullbackObj f g :=
  (Cones.forget _).mapIso <| pullbackConeIsoPullback f g

@[simp]
theorem pullback_iso_pullback_hom_fst (p : pullback f g) :
    ((pullbackIsoPullback f g).Hom p : X × Y).fst = (pullback.fst : _ ⟶ X) p :=
  congr_funₓ ((pullbackConeIsoPullback f g).Hom.w left) p

@[simp]
theorem pullback_iso_pullback_hom_snd (p : pullback f g) :
    ((pullbackIsoPullback f g).Hom p : X × Y).snd = (pullback.snd : _ ⟶ Y) p :=
  congr_funₓ ((pullbackConeIsoPullback f g).Hom.w right) p

@[simp]
theorem pullback_iso_pullback_inv_fst : (pullbackIsoPullback f g).inv ≫ pullback.fst = fun p => (p : X × Y).fst :=
  (pullbackConeIsoPullback f g).inv.w left

@[simp]
theorem pullback_iso_pullback_inv_snd : (pullbackIsoPullback f g).inv ≫ pullback.snd = fun p => (p : X × Y).snd :=
  (pullbackConeIsoPullback f g).inv.w right

end Pullback

end CategoryTheory.Limits.Types

