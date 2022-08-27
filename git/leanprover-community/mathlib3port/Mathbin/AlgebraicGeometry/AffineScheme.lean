/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.GammaSpecAdjunction
import Mathbin.AlgebraicGeometry.OpenImmersion
import Mathbin.CategoryTheory.Limits.Opposites
import Mathbin.RingTheory.Localization.InvSubmonoid

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `algebraic_geometry.AffineScheme`: The category of affine schemes.
* `algebraic_geometry.is_affine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `algebraic_geometry.Scheme.iso_Spec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `algebraic_geometry.AffineScheme.equiv_CommRing`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRing`.
* `algebraic_geometry.is_affine_open`: An open subset of a scheme is affine if the open subscheme is
  affine.
* `algebraic_geometry.is_affine_open.from_Spec`: The immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open Spec (structureSheaf)

/-- The category of affine schemes -/
@[nolint has_nonempty_instance]
def AffineScheme :=
  Scheme.spec.EssImageSubcategory deriving Category

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class IsAffine (X : Scheme) : Prop where
  affine : IsIso (ΓSpec.adjunction.Unit.app X)

attribute [instance] is_affine.affine

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
def Scheme.isoSpec (X : Scheme) [IsAffine X] : X ≅ Scheme.spec.obj (op <| Scheme.Γ.obj <| op X) :=
  asIso (ΓSpec.adjunction.Unit.app X)

/-- Construct an affine scheme from a scheme and the information that it is affine.
Also see `AffineScheme.of` for a typclass version. -/
@[simps]
def AffineScheme.mk (X : Scheme) (h : IsAffine X) : AffineScheme :=
  ⟨X, @mem_ess_image_of_unit_is_iso _ _ _ _ h.1⟩

/-- Construct an affine scheme from a scheme. Also see `AffineScheme.mk` for a non-typeclass
version. -/
def AffineScheme.of (X : Scheme) [h : IsAffine X] : AffineScheme :=
  AffineScheme.mk X h

/-- Type check a morphism of schemes as a morphism in `AffineScheme`. -/
def AffineScheme.ofHom {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) : AffineScheme.of X ⟶ AffineScheme.of Y :=
  f

theorem mem_Spec_ess_image (X : Scheme) : X ∈ Scheme.spec.EssImage ↔ IsAffine X :=
  ⟨fun h => ⟨Functor.EssImage.unit_is_iso h⟩, fun h => @mem_ess_image_of_unit_is_iso _ _ _ X h.1⟩

instance is_affine_AffineScheme (X : AffineScheme.{u}) : IsAffine X.obj :=
  ⟨Functor.EssImage.unit_is_iso X.property⟩

instance Spec_is_affine (R : CommRingₓₓᵒᵖ) : IsAffine (Scheme.spec.obj R) :=
  AlgebraicGeometry.is_affine_AffineScheme ⟨_, Scheme.spec.obj_mem_ess_image R⟩

theorem is_affine_of_iso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] [h : IsAffine Y] : IsAffine X := by
  rw [← mem_Spec_ess_image] at h⊢
  exact functor.ess_image.of_iso (as_iso f).symm h

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
def spec : CommRingₓₓᵒᵖ ⥤ AffineScheme :=
  Scheme.spec.toEssImage deriving Full, Faithful, EssSurj

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[simps]
def forgetToScheme : AffineScheme ⥤ Scheme :=
  Scheme.spec.essImageInclusion deriving Full, Faithful

/-- The global section functor of an affine scheme. -/
def Γ : AffineSchemeᵒᵖ ⥤ CommRingₓₓ :=
  forgetToScheme.op ⋙ Scheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
def equivCommRing : AffineScheme ≌ CommRingₓₓᵒᵖ :=
  equivEssImageOfReflective.symm

instance ΓIsEquiv : IsEquivalence Γ.{u} := by
  haveI : is_equivalence Γ.{u}.rightOp.op := is_equivalence.of_equivalence equiv_CommRing.op
  exact (functor.is_equivalence_trans Γ.{u}.rightOp.op (op_op_equivalence _).Functor : _)

instance : HasColimits AffineScheme.{u} := by
  haveI := Adjunction.has_limits_of_equivalence.{u} Γ.{u}
  haveI : has_colimits AffineScheme.{u}ᵒᵖᵒᵖ := has_colimits_op_of_has_limits
  exact Adjunction.has_colimits_of_equivalence.{u} (op_op_equivalence AffineScheme.{u}).inverse

instance : HasLimits AffineScheme.{u} := by
  haveI := adjunction.has_colimits_of_equivalence Γ.{u}
  haveI : has_limits AffineScheme.{u}ᵒᵖᵒᵖ := limits.has_limits_op_of_has_colimits
  exact adjunction.has_limits_of_equivalence (op_op_equivalence AffineScheme.{u}).inverse

noncomputable instance : PreservesLimits Γ.{u}.rightOp :=
  @Adjunction.isEquivalencePreservesLimits _ _ Γ.rightOp (IsEquivalence.ofEquivalence equivCommRing)

noncomputable instance : PreservesLimits forgetToScheme := by
  apply @preserves_limits_of_nat_iso _ _ (iso_whisker_right equiv_CommRing.unit_iso forget_to_Scheme).symm with
    { instances := false }
  change preserves_limits (equiv_CommRing.functor ⋙ Scheme.Spec)
  infer_instance

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
def IsAffineOpen {X : Scheme} (U : Opens X.Carrier) : Prop :=
  IsAffine (X.restrict U.OpenEmbedding)

/-- The set of affine opens as a subset of `opens X.carrier`. -/
def Scheme.AffineOpens (X : Scheme) : Set (Opens X.Carrier) :=
  { U : Opens X.Carrier | IsAffineOpen U }

theorem range_is_affine_open_of_open_immersion {X Y : Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsAffineOpen f.opensRange := by
  refine' is_affine_of_iso (is_open_immersion.iso_of_range_eq f (Y.of_restrict _) _).inv
  exact subtype.range_coe.symm
  infer_instance

theorem top_is_affine_open (X : Scheme) [IsAffine X] : IsAffineOpen (⊤ : Opens X.Carrier) := by
  convert range_is_affine_open_of_open_immersion (𝟙 X)
  ext1
  exact set.range_id.symm

instance Scheme.affine_cover_is_affine (X : Scheme) (i : X.affineCover.J) : IsAffine (X.affineCover.obj i) :=
  AlgebraicGeometry.Spec_is_affine _

instance Scheme.affine_basis_cover_is_affine (X : Scheme) (i : X.affineBasisCover.J) :
    IsAffine (X.affineBasisCover.obj i) :=
  AlgebraicGeometry.Spec_is_affine _

theorem is_basis_affine_open (X : Scheme) : Opens.IsBasis X.AffineOpens := by
  rw [opens.is_basis_iff_nbhd]
  rintro U x (hU : x ∈ (U : Set X.carrier))
  obtain ⟨S, hS, hxS, hSU⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open hU U.prop
  refine' ⟨⟨S, X.affine_basis_cover_is_basis.is_open hS⟩, _, hxS, hSU⟩
  rcases hS with ⟨i, rfl⟩
  exact range_is_affine_open_of_open_immersion _

/-- The open immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`. -/
def IsAffineOpen.fromSpec {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) :
    Scheme.spec.obj (op <| X.Presheaf.obj <| op U) ⟶ X := by
  haveI : is_affine (X.restrict U.open_embedding) := hU
  have : U.open_embedding.is_open_map.functor.obj ⊤ = U := by
    ext1
    exact set.image_univ.trans Subtype.range_coe
  exact
    Scheme.Spec.map (X.presheaf.map (eq_to_hom this.symm).op).op ≫
      (X.restrict U.open_embedding).isoSpec.inv ≫ X.of_restrict _

instance IsAffineOpen.is_open_immersion_from_Spec {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) :
    IsOpenImmersion hU.fromSpec := by
  delta' is_affine_open.from_Spec
  infer_instance

theorem IsAffineOpen.from_Spec_range {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) :
    Set.Range hU.fromSpec.1.base = (U : Set X.Carrier) := by
  delta' is_affine_open.from_Spec
  erw [← category.assoc, Scheme.comp_val_base]
  rw [coe_comp, Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ]
  exact Subtype.range_coe
  rw [← Top.epi_iff_surjective]
  infer_instance

theorem IsAffineOpen.from_Spec_image_top {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) :
    hU.is_open_immersion_from_Spec.base_open.IsOpenMap.Functor.obj ⊤ = U := by
  ext1
  exact set.image_univ.trans hU.from_Spec_range

theorem IsAffineOpen.is_compact {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) :
    IsCompact (U : Set X.Carrier) := by
  convert
    @IsCompact.image _ _ _ _ Set.Univ hU.from_Spec.1.base PrimeSpectrum.compact_space.1
      (by
        continuity)
  convert hU.from_Spec_range.symm
  exact Set.image_univ

theorem IsAffineOpen.image_is_open_immersion {X Y : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) (f : X ⟶ Y)
    [H : IsOpenImmersion f] : IsAffineOpen (f.opensFunctor.obj U) := by
  haveI : is_affine _ := hU
  convert range_is_affine_open_of_open_immersion (X.of_restrict U.open_embedding ≫ f)
  ext1
  change f.1.base '' U.1 = Set.Range (f.1.base ∘ coe)
  rw [Set.range_comp, Subtype.range_coe]

theorem is_affine_open_iff_of_is_open_immersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    (U : Opens X.Carrier) : IsAffineOpen (H.openFunctor.obj U) ↔ IsAffineOpen U := by
  refine' ⟨fun hU => @is_affine_of_iso _ _ hU, fun hU => hU.image_is_open_immersion f⟩
  refine' (is_open_immersion.iso_of_range_eq (X.of_restrict _ ≫ f) (Y.of_restrict _) _).Hom
  · rw [Scheme.comp_val_base, coe_comp, Set.range_comp]
    dsimp' [opens.inclusion]
    rw [Subtype.range_coe, Subtype.range_coe]
    rfl
    
  · infer_instance
    

instance Scheme.quasi_compact_of_affine (X : Scheme) [IsAffine X] : CompactSpace X.Carrier :=
  ⟨(top_is_affine_open X).IsCompact⟩

theorem IsAffineOpen.from_Spec_base_preimage {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) :
    (Opens.map hU.fromSpec.val.base).obj U = ⊤ := by
  ext1
  change hU.from_Spec.1.base ⁻¹' (U : Set X.carrier) = Set.Univ
  rw [← hU.from_Spec_range, ← Set.image_univ]
  exact Set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj

theorem Scheme.Spec_map_presheaf_map_eq_to_hom {X : Scheme} {U V : Opens X.Carrier} (h : U = V) (W) :
    (Scheme.spec.map (X.Presheaf.map (eqToHom h).op).op).val.c.app W =
      eqToHom
        (by
          cases h
          dsimp'
          induction W using Opposite.rec
          congr
          ext1
          simpa) :=
  by
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _ := by
    rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]
  cases h
  refine' (Scheme.congr_app this _).trans _
  erw [category.id_comp]
  simpa [eq_to_hom_map]

theorem IsAffineOpen.Spec_Γ_identity_hom_app_from_Spec {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) :
    specΓIdentity.Hom.app (X.Presheaf.obj <| op U) ≫ hU.fromSpec.1.c.app (op U) =
      (Scheme.spec.obj _).Presheaf.map (eqToHom hU.from_Spec_base_preimage).op :=
  by
  haveI : is_affine _ := hU
  have e₁ := Spec_Γ_identity.hom.naturality (X.presheaf.map (eq_to_hom U.open_embedding_obj_top).op)
  rw [← is_iso.comp_inv_eq] at e₁
  have e₂ := Γ_Spec.adjunction_unit_app_app_top (X.restrict U.open_embedding)
  erw [← e₂] at e₁
  simp only [functor.id_map, Quiver.Hom.unop_op, functor.comp_map, ← functor.map_inv, ← op_inv,
    LocallyRingedSpace.Γ_map, category.assoc, functor.right_op_map, inv_eq_to_hom] at e₁
  delta' is_affine_open.from_Spec Scheme.iso_Spec
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app, ← e₁]
  simp_rw [category.assoc]
  erw [← X.presheaf.map_comp_assoc]
  rw [← op_comp]
  have e₃ :
    U.open_embedding.is_open_map.adjunction.counit.app U ≫ eq_to_hom U.open_embedding_obj_top.symm =
      U.open_embedding.is_open_map.functor.map (eq_to_hom U.inclusion_map_eq_top) :=
    Subsingleton.elimₓ _ _
  have e₄ : X.presheaf.map _ ≫ _ = _ :=
    (as_iso (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding))).inv.1.c.naturality_assoc
      (eq_to_hom U.inclusion_map_eq_top).op _
  erw [e₃, e₄, ← Scheme.comp_val_c_app_assoc, iso.inv_hom_id]
  simp only [eq_to_hom_map, eq_to_hom_op, Scheme.Spec_map_presheaf_map_eq_to_hom]
  erw [Scheme.Spec_map_presheaf_map_eq_to_hom, category.id_comp]
  simpa only [eq_to_hom_trans]

@[elementwise]
theorem IsAffineOpen.from_Spec_app_eq {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) :
    hU.fromSpec.1.c.app (op U) =
      specΓIdentity.inv.app (X.Presheaf.obj <| op U) ≫
        (Scheme.spec.obj _).Presheaf.map (eqToHom hU.from_Spec_base_preimage).op :=
  by
  rw [← hU.Spec_Γ_identity_hom_app_from_Spec, iso.inv_hom_id_app_assoc]

theorem IsAffineOpen.basic_open_is_affine {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U)
    (f : X.Presheaf.obj (op U)) : IsAffineOpen (X.basicOpen f) := by
  convert
    range_is_affine_open_of_open_immersion
      (Scheme.Spec.map (CommRingₓₓ.ofHom (algebraMap (X.presheaf.obj (op U)) (Localization.Away f))).op ≫ hU.from_Spec)
  ext1
  have :
    hU.from_Spec.val.base '' (hU.from_Spec.val.base ⁻¹' (X.basic_open f : Set X.carrier)) =
      (X.basic_open f : Set X.carrier) :=
    by
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left_iff_subset, hU.from_Spec_range]
    exact Scheme.basic_open_subset _ _
  rw [Scheme.hom.opens_range_coe, Scheme.comp_val_base, ← this, coe_comp, Set.range_comp]
  congr 1
  refine' (congr_arg coe <| Scheme.preimage_basic_open hU.from_Spec f).trans _
  refine' Eq.trans _ (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm
  congr 1
  have : (opens.map hU.from_Spec.val.base).obj U = ⊤ := by
    ext1
    change hU.from_Spec.1.base ⁻¹' (U : Set X.carrier) = Set.Univ
    rw [← hU.from_Spec_range, ← Set.image_univ]
    exact Set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj
  refine' Eq.trans _ (basic_open_eq_of_affine f)
  have lm : ∀ s, (opens.map hU.from_Spec.val.base).obj U⊓s = s := fun s => this.symm ▸ top_inf_eq
  refine' Eq.trans _ (lm _)
  refine' Eq.trans _ ((Scheme.Spec.obj <| op <| X.presheaf.obj <| op U).basic_open_res _ (eq_to_hom this).op)
  rw [← comp_apply]
  congr 2
  rw [iso.eq_inv_comp]
  erw [hU.Spec_Γ_identity_hom_app_from_Spec]

theorem IsAffineOpen.map_restrict_basic_open {X : Scheme} (r : X.Presheaf.obj (op ⊤)) {U : Opens X.Carrier}
    (hU : IsAffineOpen U) : IsAffineOpen ((Opens.map (X.ofRestrict (X.basicOpen r).OpenEmbedding).1.base).obj U) := by
  apply (is_affine_open_iff_of_is_open_immersion (X.of_restrict (X.basic_open r).OpenEmbedding) _).mp
  delta' PresheafedSpace.is_open_immersion.open_functor
  dsimp'
  rw [opens.functor_obj_map_obj, opens.open_embedding_obj_top, inf_comm, ← opens.inter_eq, ←
    Scheme.basic_open_res _ _ (hom_of_le le_top).op]
  exact hU.basic_open_is_affine _

theorem Scheme.map_prime_spectrum_basic_open_of_affine (X : Scheme) [IsAffine X] (f : Scheme.Γ.obj (op X)) :
    (Opens.map X.isoSpec.Hom.1.base).obj (PrimeSpectrum.basicOpen f) = X.basicOpen f := by
  rw [← basic_open_eq_of_affine]
  trans
    (opens.map X.iso_Spec.hom.1.base).obj
      ((Scheme.Spec.obj (op (Scheme.Γ.obj (op X)))).basicOpen
        ((inv (X.iso_Spec.hom.1.c.app (op ((opens.map (inv X.iso_Spec.hom).val.base).obj ⊤))))
          ((X.presheaf.map (eq_to_hom _)) f)))
  congr
  · rw [← is_iso.inv_eq_inv, is_iso.inv_inv, is_iso.iso.inv_inv, nat_iso.app_hom]
    erw [← Γ_Spec.adjunction_unit_app_app_top]
    rfl
    
  · rw [eq_to_hom_map]
    rfl
    
  · dsimp'
    congr
    
  · refine' (Scheme.preimage_basic_open _ _).trans _
    rw [is_iso.inv_hom_id_apply, Scheme.basic_open_res_eq]
    

theorem is_basis_basic_open (X : Scheme) [IsAffine X] :
    Opens.IsBasis (Set.Range (X.basicOpen : X.Presheaf.obj (op ⊤) → Opens X.Carrier)) := by
  delta' opens.is_basis
  convert
    prime_spectrum.is_basis_basic_opens.inducing
      (Top.homeoOfIso (Scheme.forget_to_Top.map_iso X.iso_Spec)).Inducing using
    1
  ext
  simp only [Set.mem_image, exists_exists_eq_and]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine' ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, _⟩
    exact congr_arg Subtype.val (X.map_prime_spectrum_basic_open_of_affine x)
    
  · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    refine' ⟨_, ⟨x, rfl⟩, _⟩
    exact congr_arg Subtype.val (X.map_prime_spectrum_basic_open_of_affine x).symm
    

theorem IsAffineOpen.exists_basic_open_subset {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U)
    {V : Opens X.Carrier} (x : V) (h : ↑x ∈ U) : ∃ f : X.Presheaf.obj (op U), X.basicOpen f ⊆ V ∧ ↑x ∈ X.basicOpen f :=
  by
  haveI : is_affine _ := hU
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂⟩ :=
    (is_basis_basic_open (X.restrict U.open_embedding)).exists_subset_of_mem_open _ ((opens.map U.inclusion).obj V).Prop
  swap
  exact ⟨x, h⟩
  have :
    U.open_embedding.is_open_map.functor.obj ((X.restrict U.open_embedding).basicOpen r) =
      X.basic_open (X.presheaf.map (eq_to_hom U.open_embedding_obj_top.symm).op r) :=
    by
    refine' (Scheme.image_basic_open (X.of_restrict U.open_embedding) r).trans _
    erw [← Scheme.basic_open_res_eq _ _ (eq_to_hom U.open_embedding_obj_top).op]
    rw [← comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, eq_to_hom_trans, eq_to_hom_refl, op_id,
      CategoryTheory.Functor.map_id]
    erw [PresheafedSpace.is_open_immersion.of_restrict_inv_app]
    congr
  use X.presheaf.map (eq_to_hom U.open_embedding_obj_top.symm).op r
  rw [← this]
  exact ⟨set.image_subset_iff.mpr h₂, Set.mem_image_of_mem _ h₁⟩
  exact x.prop

instance {X : Scheme} {U : Opens X.Carrier} (f : X.Presheaf.obj (op U)) :
    Algebra (X.Presheaf.obj (op U)) (X.Presheaf.obj (op <| X.basicOpen f)) :=
  (X.Presheaf.map (hom_of_le <| RingedSpace.basic_open_subset _ f : _ ⟶ U).op).toAlgebra

theorem IsAffineOpen.opens_map_from_Spec_basic_open {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U)
    (f : X.Presheaf.obj (op U)) :
    (Opens.map hU.fromSpec.val.base).obj (X.basicOpen f) =
      RingedSpace.basicOpen _ (specΓIdentity.inv.app (X.Presheaf.obj <| op U) f) :=
  by
  erw [LocallyRingedSpace.preimage_basic_open]
  refine'
    Eq.trans _
      (RingedSpace.basic_open_res_eq (Scheme.Spec.obj <| op <| X.presheaf.obj (op U)).toLocallyRingedSpace.toRingedSpace
        (eq_to_hom hU.from_Spec_base_preimage).op _)
  congr
  rw [← comp_apply]
  congr
  erw [← hU.Spec_Γ_identity_hom_app_from_Spec]
  rw [iso.inv_hom_id_app_assoc]

/-- The canonical map `Γ(𝒪ₓ, D(f)) ⟶ Γ(Spec 𝒪ₓ(U), D(Spec_Γ_identity.inv f))`
This is an isomorphism, as witnessed by an `is_iso` instance. -/
def basicOpenSectionsToAffine {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) (f : X.Presheaf.obj (op U)) :
    X.Presheaf.obj (op <| X.basicOpen f) ⟶
      (Scheme.spec.obj <| op <| X.Presheaf.obj (op U)).Presheaf.obj
        (op <| Scheme.basicOpen _ <| specΓIdentity.inv.app (X.Presheaf.obj (op U)) f) :=
  hU.fromSpec.1.c.app (op <| X.basicOpen f) ≫
    (Scheme.spec.obj <| op <| X.Presheaf.obj (op U)).Presheaf.map
      (eq_to_hom <| (hU.opens_map_from_Spec_basic_open f).symm).op

instance {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) (f : X.Presheaf.obj (op U)) :
    IsIso (basicOpenSectionsToAffine hU f) := by
  delta' basic_open_sections_to_affine
  apply is_iso.comp_is_iso with { instances := false }
  · apply PresheafedSpace.is_open_immersion.is_iso_of_subset
    rw [hU.from_Spec_range]
    exact RingedSpace.basic_open_subset _ _
    
  infer_instance

theorem is_localization_basic_open {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U)
    (f : X.Presheaf.obj (op U)) : IsLocalization.Away f (X.Presheaf.obj (op <| X.basicOpen f)) := by
  apply
    (IsLocalization.is_localization_iff_of_ring_equiv (Submonoid.powers f)
        (as_iso <|
            basic_open_sections_to_affine hU f ≫
              (Scheme.Spec.obj _).Presheaf.map
                (eq_to_hom (basic_open_eq_of_affine _).symm).op).commRingIsoToRingEquiv).mpr
  convert structure_sheaf.is_localization.to_basic_open _ f
  change _ ≫ basic_open_sections_to_affine hU f ≫ _ = _
  delta' basic_open_sections_to_affine
  erw [RingHom.algebra_map_to_algebra]
  simp only [Scheme.comp_val_c_app, category.assoc]
  erw [hU.from_Spec.val.c.naturality_assoc]
  rw [hU.from_Spec_app_eq]
  dsimp'
  simp only [category.assoc, ← functor.map_comp, ← op_comp]
  apply structure_sheaf.to_open_res

instance {X : Scheme} [IsAffine X] (r : X.Presheaf.obj (op ⊤)) :
    IsLocalization.Away r (X.Presheaf.obj (op <| X.basicOpen r)) :=
  is_localization_basic_open (top_is_affine_open X) r

theorem is_localization_of_eq_basic_open {X : Scheme} {U V : Opens X.Carrier} (i : V ⟶ U) (hU : IsAffineOpen U)
    (r : X.Presheaf.obj (op U)) (e : V = X.basicOpen r) :
    @IsLocalization.Away _ r (X.Presheaf.obj (op V)) _ (X.Presheaf.map i.op).toAlgebra := by
  subst e
  convert is_localization_basic_open hU r using 3

instance ΓRestrictAlgebra {X : Scheme} {Y : Top} {f : Y ⟶ X.Carrier} (hf : OpenEmbedding f) :
    Algebra (Scheme.Γ.obj (op X)) (Scheme.Γ.obj (op <| X.restrict hf)) :=
  (Scheme.Γ.map (X.ofRestrict hf).op).toAlgebra

instance Γ_restrict_is_localization (X : Scheme.{u}) [IsAffine X] (r : Scheme.Γ.obj (op X)) :
    IsLocalization.Away r (Scheme.Γ.obj (op <| X.restrict (X.basicOpen r).OpenEmbedding)) :=
  is_localization_of_eq_basic_open _ (top_is_affine_open X) r (Opens.open_embedding_obj_top _)

theorem basic_open_basic_open_is_basic_open {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U)
    (f : X.Presheaf.obj (op U)) (g : X.Presheaf.obj (op <| X.basicOpen f)) :
    ∃ f' : X.Presheaf.obj (op U), X.basicOpen f' = X.basicOpen g := by
  haveI := is_localization_basic_open hU f
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.surj' (Submonoid.powers f) g
  use f * x
  rw [Algebra.smul_def, Scheme.basic_open_mul, Scheme.basic_open_mul]
  erw [Scheme.basic_open_res]
  refine' (inf_eq_left.mpr _).symm
  convert inf_le_left using 1
  apply Scheme.basic_open_of_is_unit
  apply
    Submonoid.left_inv_le_is_unit _
      (IsLocalization.toInvSubmonoid (Submonoid.powers f) (X.presheaf.obj (op <| X.basic_open f)) _).Prop

theorem exists_basic_open_subset_affine_inter {X : Scheme} {U V : Opens X.Carrier} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (x : X.Carrier) (hx : x ∈ U ∩ V) :
    ∃ (f : X.Presheaf.obj <| op U)(g : X.Presheaf.obj <| op V), X.basicOpen f = X.basicOpen g ∧ x ∈ X.basicOpen f := by
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basic_open_subset ⟨x, hx.2⟩ hx.1
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basic_open_subset ⟨x, hf₂⟩ hx.2
  obtain ⟨f', hf'⟩ := basic_open_basic_open_is_basic_open hU f (X.presheaf.map (hom_of_le hf₁ : _ ⟶ V).op g)
  replace hf' := (hf'.trans (RingedSpace.basic_open_res _ _ _)).trans (inf_eq_right.mpr hg₁)
  exact ⟨f', g, hf', hf'.symm ▸ hg₂⟩

/-- The prime ideal of `𝒪ₓ(U)` corresponding to a point `x : U`. -/
noncomputable def IsAffineOpen.primeIdealOf {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) (x : U) :
    PrimeSpectrum (X.Presheaf.obj <| op U) :=
  (Scheme.spec.map
          (X.Presheaf.map
              (eq_to_hom <|
                  show U.OpenEmbedding.IsOpenMap.Functor.obj ⊤ = U from
                    Opens.ext (Set.image_univ.trans Subtype.range_coe)).op).op).1.base
    ((@Scheme.isoSpec (X.restrict U.OpenEmbedding) hU).Hom.1.base x)

theorem IsAffineOpen.from_Spec_prime_ideal_of {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) (x : U) :
    hU.fromSpec.val.base (hU.primeIdealOf x) = x.1 := by
  dsimp' only [is_affine_open.from_Spec, Subtype.coe_mk]
  erw [← Scheme.comp_val_base_apply, ← Scheme.comp_val_base_apply]
  simpa only [← functor.map_comp_assoc, ← functor.map_comp, ← op_comp, eq_to_hom_trans, op_id, eq_to_hom_refl,
    CategoryTheory.Functor.map_id, category.id_comp, iso.hom_inv_id_assoc]

theorem IsAffineOpen.is_localization_stalk_aux {X : Scheme} (U : Opens X.Carrier)
    [IsAffine (X.restrict U.OpenEmbedding)] :
    (inv (ΓSpec.adjunction.Unit.app (X.restrict U.OpenEmbedding))).1.c.app (op ((Opens.map U.inclusion).obj U)) =
      X.Presheaf.map
          (eq_to_hom <| by
              rw [opens.inclusion_map_eq_top] :
              U.OpenEmbedding.IsOpenMap.Functor.obj ⊤ ⟶
                U.OpenEmbedding.IsOpenMap.Functor.obj ((Opens.map U.inclusion).obj U)).op ≫
        toSpecΓ (X.Presheaf.obj <| op (U.OpenEmbedding.IsOpenMap.Functor.obj ⊤)) ≫
          (Scheme.spec.obj <| op <| X.Presheaf.obj <| _).Presheaf.map
            (eqToHom
                (by
                  rw [opens.inclusion_map_eq_top]
                  rfl) :
                unop _ ⟶ ⊤).op :=
  by
  have e :
    (opens.map (inv (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding))).1.base).obj
        ((opens.map U.inclusion).obj U) =
      ⊤ :=
    by
    rw [opens.inclusion_map_eq_top]
    rfl
  rw [Scheme.inv_val_c_app, is_iso.comp_inv_eq, Scheme.app_eq _ e, Γ_Spec.adjunction_unit_app_app_top]
  simp only [category.assoc, eq_to_hom_op]
  erw [← functor.map_comp_assoc]
  rw [eq_to_hom_trans, eq_to_hom_refl, CategoryTheory.Functor.map_id, category.id_comp]
  erw [Spec_Γ_identity.inv_hom_id_app_assoc]
  simp only [eq_to_hom_map, eq_to_hom_trans]

theorem IsAffineOpen.is_localization_stalk {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U) (x : U) :
    IsLocalization.AtPrime (X.Presheaf.stalk x) (hU.primeIdealOf x).asIdeal := by
  haveI : is_affine _ := hU
  haveI : Nonempty U := ⟨x⟩
  rcases x with ⟨x, hx⟩
  let y := hU.prime_ideal_of ⟨x, hx⟩
  have : hU.from_Spec.val.base y = x := hU.from_Spec_prime_ideal_of ⟨x, hx⟩
  change IsLocalization y.as_ideal.prime_compl _
  clear_value y
  subst this
  apply
    (IsLocalization.is_localization_iff_of_ring_equiv _
        (as_iso <| PresheafedSpace.stalk_map hU.from_Spec.1 y).commRingIsoToRingEquiv).mpr
  convert structure_sheaf.is_localization.to_stalk _ _ using 1
  delta' structure_sheaf.stalk_algebra
  congr 1
  rw [RingHom.algebra_map_to_algebra]
  refine' (PresheafedSpace.stalk_map_germ hU.from_Spec.1 _ ⟨_, _⟩).trans _
  delta' is_affine_open.from_Spec Scheme.iso_Spec structure_sheaf.to_stalk
  simp only [Scheme.comp_val_c_app, category.assoc]
  dsimp' only [functor.op, as_iso_inv, unop_op]
  erw [is_affine_open.is_localization_stalk_aux]
  simp only [category.assoc]
  conv_lhs => rw [← category.assoc]
  erw [← X.presheaf.map_comp, Spec_Γ_naturality_assoc]
  congr 1
  simp only [← category.assoc]
  trans _ ≫ (structure_sheaf (X.presheaf.obj <| op U)).Presheaf.germ ⟨_, _⟩
  · rfl
    
  convert (structure_sheaf (X.presheaf.obj <| op U)).Presheaf.germ_res (hom_of_le le_top) ⟨_, _⟩ using 2
  rw [category.assoc]
  erw [nat_trans.naturality]
  rw [← LocallyRingedSpace.Γ_map_op, ← LocallyRingedSpace.Γ.map_comp_assoc, ← op_comp]
  erw [← Scheme.Spec.map_comp]
  rw [← op_comp, ← X.presheaf.map_comp]
  trans LocallyRingedSpace.Γ.map (Quiver.Hom.op <| Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op) ≫ _
  · congr
    
  simp only [CategoryTheory.Functor.map_id, op_id]
  erw [CategoryTheory.Functor.map_id]
  rw [category.id_comp]
  rfl

/-- The basic open set of a section `f` on an an affine open as an `X.affine_opens`. -/
@[simps]
def Scheme.affineBasicOpen (X : Scheme) {U : X.AffineOpens} (f : X.Presheaf.obj <| op U) : X.AffineOpens :=
  ⟨X.basicOpen f, U.Prop.basic_open_is_affine f⟩

@[simp]
theorem IsAffineOpen.basic_open_from_Spec_app {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U)
    (f : X.Presheaf.obj (op U)) :
    @Scheme.basicOpen (Scheme.spec.obj <| op (X.Presheaf.obj <| op U)) ((Opens.map hU.fromSpec.1.base).obj U)
        (hU.fromSpec.1.c.app (op U) f) =
      PrimeSpectrum.basicOpen f :=
  by
  rw [← Scheme.basic_open_res_eq _ _ (eq_to_hom hU.from_Spec_base_preimage.symm).op, basic_open_eq_of_affine',
    is_affine_open.from_Spec_app_eq]
  congr
  rw [← comp_apply, ← comp_apply, category.assoc, ← functor.map_comp_assoc, eq_to_hom_op, eq_to_hom_op, eq_to_hom_trans,
    eq_to_hom_refl, CategoryTheory.Functor.map_id, category.id_comp, ← iso.app_inv, iso.inv_hom_id]
  rfl

theorem IsAffineOpen.from_Spec_map_basic_open {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U)
    (f : X.Presheaf.obj (op U)) : (Opens.map hU.fromSpec.val.base).obj (X.basicOpen f) = PrimeSpectrum.basicOpen f := by
  simp

theorem IsAffineOpen.basic_open_union_eq_self_iff {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U)
    (s : Set (X.Presheaf.obj <| op U)) : (⨆ f : s, X.basicOpen (f : X.Presheaf.obj <| op U)) = U ↔ Ideal.span s = ⊤ :=
  by
  trans (⋃ i : s, (PrimeSpectrum.basicOpen i.1).1) = Set.Univ
  trans hU.from_Spec.1.base ⁻¹' (⨆ f : s, X.basic_open (f : X.presheaf.obj <| op U)).1 = hU.from_Spec.1.base ⁻¹' U.1
  · refine'
      ⟨fun h => by
        rw [h], _⟩
    intro h
    apply_fun Set.Image hU.from_Spec.1.base  at h
    rw [Set.image_preimage_eq_inter_range, Set.image_preimage_eq_inter_range, hU.from_Spec_range] at h
    simp only [Set.inter_self, Subtype.val_eq_coe, Set.inter_eq_right_iff_subset] at h
    ext1
    refine' le_antisymmₓ _ h
    simp only [Set.Union_subset_iff, SetCoe.forall, opens.supr_def, Set.le_eq_subset, Subtype.coe_mk]
    intro x hx
    exact X.basic_open_subset x
    
  · simp only [opens.supr_def, Subtype.coe_mk, Set.preimage_Union, Subtype.val_eq_coe]
    congr 3
    · ext1 x
      exact congr_arg Subtype.val (hU.from_Spec_map_basic_open _)
      
    · exact congr_arg Subtype.val hU.from_Spec_base_preimage
      
    
  · simp only [Subtype.val_eq_coe, PrimeSpectrum.basic_open_eq_zero_locus_compl]
    rw [← Set.compl_Inter, Set.compl_univ_iff, ← PrimeSpectrum.zero_locus_Union, ←
      PrimeSpectrum.zero_locus_empty_iff_eq_top, PrimeSpectrum.zero_locus_span]
    simp only [Set.Union_singleton_eq_range, Subtype.range_coe_subtype, Set.set_of_mem_eq]
    

theorem IsAffineOpen.self_le_basic_open_union_iff {X : Scheme} {U : Opens X.Carrier} (hU : IsAffineOpen U)
    (s : Set (X.Presheaf.obj <| op U)) : (U ≤ ⨆ f : s, X.basicOpen (f : X.Presheaf.obj <| op U)) ↔ Ideal.span s = ⊤ :=
  by
  rw [← hU.basic_open_union_eq_self_iff, @comm _ Eq]
  refine' ⟨fun h => le_antisymmₓ h _, le_of_eqₓ⟩
  simp only [supr_le_iff, SetCoe.forall]
  intro x hx
  exact X.basic_open_subset x

/-- Let `P` be a predicate on the affine open sets of `X` satisfying
1. If `P` holds on `U`, then `P` holds on the basic open set of every section on `U`.
2. If `P` holds for a family of basic open sets covering `U`, then `P` holds for `U`.
3. There exists an affine open cover of `X` each satisfying `P`.

Then `P` holds for every affine open of `X`.

This is also known as the **Affine communication lemma** in Vakil's "The rising sea". -/
@[elabAsElim]
theorem of_affine_open_cover {X : Scheme} (V : X.AffineOpens) (S : Set X.AffineOpens) {P : X.AffineOpens → Prop}
    (hP₁ : ∀ (U : X.AffineOpens) (f : X.Presheaf.obj <| op U.1), P U → P (X.affineBasicOpen f))
    (hP₂ :
      ∀ (U : X.AffineOpens) (s : Finset (X.Presheaf.obj <| op U))
        (hs : Ideal.span (s : Set (X.Presheaf.obj <| op U)) = ⊤), (∀ f : s, P (X.affineBasicOpen f.1)) → P U)
    (hS : (⋃ i : S, i : Set X.Carrier) = Set.Univ) (hS' : ∀ U : S, P U) : P V := by
  classical
  have : ∀ x : V, ∃ f : X.presheaf.obj <| op V.1, ↑x ∈ X.basic_open f ∧ P (X.affine_basic_open f) := by
    intro x
    have : ↑x ∈ (Set.Univ : Set X.carrier) := trivialₓ
    rw [← hS] at this
    obtain ⟨W, hW⟩ := set.mem_Union.mp this
    obtain ⟨f, g, e, hf⟩ := exists_basic_open_subset_affine_inter V.prop W.1.Prop x ⟨x.prop, hW⟩
    refine' ⟨f, hf, _⟩
    convert hP₁ _ g (hS' W) using 1
    ext1
    exact e
  choose f hf₁ hf₂ using this
  suffices Ideal.span (Set.Range f) = ⊤ by
    obtain ⟨t, ht₁, ht₂⟩ := (Ideal.span_eq_top_iff_finite _).mp this
    apply hP₂ V t ht₂
    rintro ⟨i, hi⟩
    obtain ⟨x, rfl⟩ := ht₁ hi
    exact hf₂ x
  rw [← V.prop.self_le_basic_open_union_iff]
  intro x hx
  simp only [exists_prop, Set.mem_Union, Set.mem_range, SetCoe.exists, opens.supr_def, exists_exists_eq_and,
    opens.mem_coe, Subtype.coe_mk]
  refine' ⟨_, hf₁ ⟨x, hx⟩⟩

end AlgebraicGeometry

