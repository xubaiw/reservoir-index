/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.Morphisms.Basic
import Mathbin.RingTheory.LocalProperties

/-!

# Properties of morphisms from properties of ring homs.

We provide the basic framework for talking about properties of morphisms that come from properties
of ring homs. For `P` a property of ring homs, we have two ways of defining a property of scheme
morphisms:

Let `f : X ⟶ Y`,
- `target_affine_locally (affine_and P)`: the preimage of an affine open `U = Spec A` is affine
  (`= Spec B`) and `A ⟶ B` satisfies `P`. (TODO)
- `affine_locally P`: For each pair of affine open `U = Spec A ⊆ X` and `V = Spec B ⊆ f ⁻¹' U`,
  the ring hom `A ⟶ B` satisfies `P`.

For these notions to be well defined, we require `P` be a sufficient local property. For the former,
`P` should be local on the source (`ring_hom.respects_iso P`, `ring_hom.localization_preserves P`,
`ring_hom.of_localization_span`), and `target_affine_locally (affine_and P)` will be local on
the target. (TODO)

For the latter `P` should be local on the target (`ring_hom.property_is_local P`), and
`affine_locally P` will be local on both the source and the target.

Further more, these properties are stable under compositions (resp. base change) if `P` is. (TODO)

-/


universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits AlgebraicGeometry

variable (P : ∀ {R S : Type u} [CommRingₓ R] [CommRingₓ S] (f : R →+* S), Prop)

namespace RingHom

include P

variable {P}

theorem RespectsIso.basic_open_iff (hP : RespectsIso @P) {X Y : Scheme} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (r : Y.Presheaf.obj (Opposite.op ⊤)) :
    P (Scheme.Γ.map (f ∣_ Y.basicOpen r).op) ↔
      P
        (@IsLocalization.Away.map (Y.Presheaf.obj (Opposite.op ⊤)) _ (Y.Presheaf.obj (Opposite.op <| Y.basicOpen r)) _ _
          (X.Presheaf.obj (Opposite.op ⊤)) _ (X.Presheaf.obj (Opposite.op <| X.basicOpen (Scheme.Γ.map f.op r))) _ _
          (Scheme.Γ.map f.op) r _ _) :=
  by
  rw [Γ_map_morphism_restrict, hP.cancel_left_is_iso, hP.cancel_right_is_iso, ←
    hP.cancel_right_is_iso (f.val.c.app (Opposite.op (Y.basic_open r)))
      (X.presheaf.map (eq_to_hom (Scheme.preimage_basic_open f r).symm).op),
    ← eq_iff_iff]
  congr
  delta' IsLocalization.Away.map
  refine' IsLocalization.ring_hom_ext (Submonoid.powers r) _
  convert (IsLocalization.map_comp _).symm using 1
  change Y.presheaf.map _ ≫ _ = _ ≫ X.presheaf.map _
  rw [f.val.c.naturality_assoc]
  erw [← X.presheaf.map_comp]
  congr

theorem RespectsIso.basic_open_iff_localization (hP : RespectsIso @P) {X Y : Scheme} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (r : Y.Presheaf.obj (Opposite.op ⊤)) :
    P (Scheme.Γ.map (f ∣_ Y.basicOpen r).op) ↔ P (Localization.awayMap (Scheme.Γ.map f.op) r) :=
  (hP.basic_open_iff _ _).trans (hP.is_localization_away_iff _ _ _ _).symm

theorem RespectsIso.of_restrict_morphism_restrict_iff (hP : RingHom.RespectsIso @P) {X Y : Scheme} [IsAffine Y]
    (f : X ⟶ Y) (r : Y.Presheaf.obj (Opposite.op ⊤)) (U : Opens X.Carrier) (hU : IsAffineOpen U) {V : Opens _}
    (e : V = (Opens.map (X.ofRestrict ((Opens.map f.1.base).obj _).OpenEmbedding).1.base).obj U) :
    P
        (Scheme.Γ.map
          ((X.restrict ((Opens.map f.1.base).obj _).OpenEmbedding).ofRestrict V.OpenEmbedding ≫
              f ∣_ Y.basicOpen r).op) ↔
      P (Localization.awayMap (Scheme.Γ.map (X.ofRestrict U.OpenEmbedding ≫ f).op) r) :=
  by
  subst e
  convert (hP.is_localization_away_iff _ _ _ _).symm
  rotate_left
  · infer_instance
    
  · apply RingHom.toAlgebra
    refine' X.presheaf.map (@hom_of_le _ _ ((IsOpenMap.functor _).obj _) ((IsOpenMap.functor _).obj _) _).op
    rw [opens.le_def]
    dsimp'
    change coe '' (coe '' Set.Univ) ⊆ coe '' Set.Univ
    rw [Subtype.coe_image_univ, Subtype.coe_image_univ]
    exact Set.image_preimage_subset _ _
    
  · exact AlgebraicGeometry.Γ_restrict_is_localization Y r
    
  · rw [← U.open_embedding_obj_top] at hU
    dsimp' [Scheme.Γ_obj_op, Scheme.Γ_map_op, Scheme.restrict]
    apply AlgebraicGeometry.is_localization_of_eq_basic_open _ hU
    rw [opens.open_embedding_obj_top, opens.functor_obj_map_obj]
    convert (X.basic_open_res (Scheme.Γ.map f.op r) (hom_of_le le_top).op).symm using 1
    rw [opens.open_embedding_obj_top, opens.open_embedding_obj_top, inf_comm, Scheme.Γ_map_op, ←
      Scheme.preimage_basic_open]
    rfl
    
  · apply IsLocalization.ring_hom_ext (Submonoid.powers r) _
    swap
    · exact AlgebraicGeometry.Γ_restrict_is_localization Y r
      
    rw [IsLocalization.Away.map, IsLocalization.map_comp, RingHom.algebra_map_to_algebra,
      RingHom.algebra_map_to_algebra, op_comp, functor.map_comp, op_comp, functor.map_comp]
    refine' (@category.assoc CommRingₓₓ _ _ _ _ _ _ _ _).symm.trans _
    refine' Eq.trans _ (@category.assoc CommRingₓₓ _ _ _ _ _ _ _ _)
    dsimp' only [Scheme.Γ_map, Quiver.Hom.unop_op]
    rw [morphism_restrict_c_app, category.assoc, category.assoc, category.assoc]
    erw [f.1.c.naturality_assoc, ← X.presheaf.map_comp, ← X.presheaf.map_comp, ← X.presheaf.map_comp]
    congr
    

theorem StableUnderBaseChange.Γ_pullback_fst (hP : StableUnderBaseChange @P) (hP' : RespectsIso @P) {X Y S : Scheme}
    [IsAffine X] [IsAffine Y] [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S) (H : P (Scheme.Γ.map g.op)) :
    P (Scheme.Γ.map (pullback.fst : pullback f g ⟶ _).op) := by
  rw [← preserves_pullback.iso_inv_fst AffineScheme.forget_to_Scheme (AffineScheme.of_hom f) (AffineScheme.of_hom g),
    op_comp, functor.map_comp, hP'.cancel_right_is_iso, AffineScheme.forget_to_Scheme_map]
  have :=
    _root_.congr_arg Quiver.Hom.unop
      (preserves_pullback.iso_hom_fst AffineScheme.Γ.right_op (AffineScheme.of_hom f) (AffineScheme.of_hom g))
  simp only [Quiver.Hom.unop_op, functor.right_op_map, unop_comp] at this
  delta' AffineScheme.Γ  at this
  simp only [Quiver.Hom.unop_op, functor.comp_map, AffineScheme.forget_to_Scheme_map, functor.op_map] at this
  rw [← this, hP'.cancel_right_is_iso, ← pushout_iso_unop_pullback_inl_hom (Quiver.Hom.unop _) (Quiver.Hom.unop _),
    hP'.cancel_right_is_iso]
  exact hP.pushout_inl _ hP' _ _ H

end RingHom

namespace AlgebraicGeometry

/-- For `P` a property of ring homomorphisms, `source_affine_locally P` holds for `f : X ⟶ Y`
whenever `P` holds for the restriction of `f` on every affine open subset of `X`. -/
def SourceAffineLocally : AffineTargetMorphismProperty := fun X Y f hY =>
  ∀ U : X.AffineOpens, P (Scheme.Γ.map (X.ofRestrict U.1.OpenEmbedding ≫ f).op)

/-- For `P` a property of ring homomorphisms, `affine_locally P` holds for `f : X ⟶ Y` if for each
affine open `U = Spec A ⊆ Y` and `V = Spec B ⊆ f ⁻¹' U`, the ring hom `A ⟶ B` satisfies `P`.
Also see `affine_locally_iff_affine_opens_le`. -/
abbrev AffineLocally : MorphismProperty Scheme :=
  TargetAffineLocally (SourceAffineLocally @P)

variable {P}

theorem source_affine_locally_respects_iso (h₁ : RingHom.RespectsIso @P) :
    (SourceAffineLocally @P).ToProperty.RespectsIso := by
  apply affine_target_morphism_property.respects_iso_mk
  · introv H U
    rw [← h₁.cancel_right_is_iso _ (Scheme.Γ.map (Scheme.restrict_map_iso e.inv U.1).Hom.op), ← functor.map_comp, ←
      op_comp]
    convert H ⟨_, U.prop.map_is_iso e.inv⟩ using 3
    rw [is_open_immersion.iso_of_range_eq_hom, is_open_immersion.lift_fac_assoc, category.assoc, e.inv_hom_id_assoc]
    rfl
    
  · introv H U
    rw [← category.assoc, op_comp, functor.map_comp, h₁.cancel_left_is_iso]
    exact H U
    

theorem affine_locally_respects_iso (h : RingHom.RespectsIso @P) : (AffineLocally @P).RespectsIso :=
  target_affine_locally_respects_iso (source_affine_locally_respects_iso h)

theorem affine_locally_iff_affine_opens_le (hP : RingHom.RespectsIso @P) {X Y : Scheme} (f : X ⟶ Y) :
    AffineLocally (@P) f ↔
      ∀ (U : Y.AffineOpens) (V : X.AffineOpens) (e : V.1 ≤ (Opens.map f.1.base).obj U.1),
        P (f.1.c.app (op U) ≫ X.Presheaf.map (homOfLe e).op) :=
  by
  apply forall_congrₓ
  intro U
  delta' source_affine_locally
  simp_rw [op_comp, Scheme.Γ.map_comp, Γ_map_morphism_restrict, category.assoc, Scheme.Γ_map_op, hP.cancel_left_is_iso]
  constructor
  · intro H V e
    let U' := (opens.map f.val.base).obj U.1
    have e' : U'.open_embedding.is_open_map.functor.obj ((opens.map U'.inclusion).obj V.1) = V.1 := by
      ext1
      refine' set.image_preimage_eq_inter_range.trans (set.inter_eq_left_iff_subset.mpr _)
      convert e
      exact Subtype.range_coe
    have := H ⟨(opens.map (X.of_restrict U'.open_embedding).1.base).obj V.1, _⟩
    erw [← X.presheaf.map_comp] at this
    rw [← hP.cancel_right_is_iso _ (X.presheaf.map (eq_to_hom _)), category.assoc, ← X.presheaf.map_comp]
    convert this using 1
    · dsimp' only [functor.op, unop_op]
      rw [opens.open_embedding_obj_top]
      congr 1
      exact e'.symm
      
    · infer_instance
      
    · apply (is_affine_open_iff_of_is_open_immersion (X.of_restrict _) _).mp
      convert V.2
      infer_instance
      
    
  · intro H V
    specialize H ⟨_, V.2.image_is_open_immersion (X.of_restrict _)⟩ (Subtype.coe_image_subset _ _)
    erw [← X.presheaf.map_comp]
    rw [← hP.cancel_right_is_iso _ (X.presheaf.map (eq_to_hom _)), category.assoc, ← X.presheaf.map_comp]
    convert H
    · dsimp' only [functor.op, unop_op]
      rw [opens.open_embedding_obj_top]
      rfl
      
    · infer_instance
      
    

theorem Scheme_restrict_basic_open_of_localization_preserves (h₁ : RingHom.RespectsIso @P)
    (h₂ : RingHom.LocalizationPreserves @P) {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Y.Presheaf.obj (op ⊤))
    (H : SourceAffineLocally (@P) f)
    (U : (X.restrict ((Opens.map f.1.base).obj <| Y.basicOpen r).OpenEmbedding).AffineOpens) :
    P
      (Scheme.Γ.map
        ((X.restrict ((Opens.map f.1.base).obj <| Y.basicOpen r).OpenEmbedding).ofRestrict U.1.OpenEmbedding ≫
            f ∣_ Y.basicOpen r).op) :=
  by
  specialize H ⟨_, U.2.image_is_open_immersion (X.of_restrict _)⟩
  convert (h₁.of_restrict_morphism_restrict_iff _ _ _ _ _).mpr _ using 1
  pick_goal 5
  · exact h₂.away r H
    
  · infer_instance
    
  · exact U.2.image_is_open_immersion _
    
  · ext1
    exact (Set.preimage_image_eq _ Subtype.coe_injective).symm
    

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (V «expr = » (opens.map f.val.base).obj (Y.basic_open r.val))
theorem source_affine_locally_is_local (h₁ : RingHom.RespectsIso @P) (h₂ : RingHom.LocalizationPreserves @P)
    (h₃ : RingHom.OfLocalizationSpan @P) : (SourceAffineLocally @P).IsLocal := by
  constructor
  · exact source_affine_locally_respects_iso h₁
    
  · introv H U
    apply Scheme_restrict_basic_open_of_localization_preserves h₁ h₂ <;> assumption
    
  · introv hs hs' U
    skip
    apply h₃ _ _ hs
    intro r
    have := hs' r ⟨(opens.map (X.of_restrict _).1.base).obj U.1, _⟩
    rwa [h₁.of_restrict_morphism_restrict_iff] at this
    · exact U.2
      
    · rfl
      
    · infer_instance
      
    · suffices
        ∀ (V) (_ : V = (opens.map f.val.base).obj (Y.basic_open r.val)),
          is_affine_open ((opens.map (X.of_restrict V.OpenEmbedding).1.base).obj U.1)
        by
        exact this _ rfl
      intro V hV
      rw [Scheme.preimage_basic_open] at hV
      subst hV
      exact U.2.map_restrict_basic_open (Scheme.Γ.map f.op r.1)
      
    

variable {P} (hP : RingHom.PropertyIsLocal @P)

theorem source_affine_locally_of_source_open_cover_aux (h₁ : RingHom.RespectsIso @P)
    (h₃ : RingHom.OfLocalizationSpanTarget @P) {X Y : Scheme} (f : X ⟶ Y) (U : X.AffineOpens)
    (s : Set (X.Presheaf.obj (op U.1))) (hs : Ideal.span s = ⊤)
    (hs' : ∀ r : s, P (Scheme.Γ.map (X.ofRestrict (X.basicOpen r.1).OpenEmbedding ≫ f).op)) :
    P (Scheme.Γ.map (X.ofRestrict U.1.OpenEmbedding ≫ f).op) := by
  apply_fun Ideal.map (X.presheaf.map (eq_to_hom U.1.open_embedding_obj_top).op)  at hs
  rw [Ideal.map_span, Ideal.map_top] at hs
  apply h₃ _ _ hs
  rintro ⟨s, r, hr, hs⟩
  have :=
    (@Localization.algEquiv _ _ _ _ _ (@AlgebraicGeometry.Γ_restrict_is_localization _ U.2 s)).toRingEquiv.toCommRingIso
  refine'
    (h₁.cancel_right_is_iso _
          (@Localization.algEquiv _ _ _ _ _
                  (@AlgebraicGeometry.Γ_restrict_is_localization _ U.2 s)).toRingEquiv.toCommRingIso.Hom).mp
      _
  subst hs
  rw [CommRingₓₓ.comp_eq_ring_hom_comp, ← RingHom.comp_assoc]
  erw [IsLocalization.map_comp, RingHom.comp_id]
  rw [RingHom.algebra_map_to_algebra, op_comp, functor.map_comp, ← CommRingₓₓ.comp_eq_ring_hom_comp, Scheme.Γ_map_op,
    Scheme.Γ_map_op, Scheme.Γ_map_op, category.assoc]
  erw [← X.presheaf.map_comp]
  rw [← h₁.cancel_right_is_iso _ (X.presheaf.map (eq_to_hom _))]
  convert hs' ⟨r, hr⟩ using 1
  · erw [category.assoc]
    rw [← X.presheaf.map_comp, op_comp, Scheme.Γ.map_comp, Scheme.Γ_map_op, Scheme.Γ_map_op]
    congr
    
  · dsimp' [functor.op]
    conv_lhs => rw [opens.open_embedding_obj_top]
    conv_rhs => rw [opens.open_embedding_obj_top]
    erw [Scheme.image_basic_open (X.of_restrict U.1.OpenEmbedding)]
    erw [PresheafedSpace.is_open_immersion.of_restrict_inv_app_apply]
    rw [Scheme.basic_open_res_eq]
    
  · infer_instance
    

theorem is_open_immersion_comp_of_source_affine_locally (h₁ : RingHom.RespectsIso @P) {X Y Z : Scheme} [IsAffine X]
    [IsAffine Z] (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z) (h₂ : SourceAffineLocally (@P) g) :
    P (Scheme.Γ.map (f ≫ g).op) := by
  rw [← h₁.cancel_right_is_iso _ (Scheme.Γ.map (is_open_immersion.iso_of_range_eq (Y.of_restrict _) f _).Hom.op), ←
    functor.map_comp, ← op_comp]
  convert h₂ ⟨_, range_is_affine_open_of_open_immersion f⟩ using 3
  · rw [is_open_immersion.iso_of_range_eq_hom, is_open_immersion.lift_fac_assoc]
    
  · infer_instance
    
  · exact Subtype.range_coe
    
  · infer_instance
    

end AlgebraicGeometry

open AlgebraicGeometry

namespace RingHom.PropertyIsLocal

variable {P} (hP : RingHom.PropertyIsLocal @P)

include hP

theorem source_affine_locally_of_source_open_cover {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] (𝒰 : X.OpenCover)
    [∀ i, IsAffine (𝒰.obj i)] (H : ∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op)) : SourceAffineLocally (@P) f := by
  let S := fun i =>
    (⟨⟨Set.Range (𝒰.map i).1.base, (𝒰.is_open i).base_open.open_range⟩,
      range_is_affine_open_of_open_immersion (𝒰.map i)⟩ :
      X.affine_opens)
  intro U
  apply of_affine_open_cover U
  pick_goal 5
  · exact Set.Range S
    
  · intro U r H
    convert hP.stable_under_composition _ _ H _ using 1
    swap
    · refine' X.presheaf.map (@hom_of_le _ _ ((IsOpenMap.functor _).obj _) ((IsOpenMap.functor _).obj _) _).op
      rw [unop_op, unop_op, opens.open_embedding_obj_top, opens.open_embedding_obj_top]
      exact X.basic_open_subset _
      
    · rw [op_comp, op_comp, functor.map_comp, functor.map_comp]
      refine' (Eq.trans _ (category.assoc _ _ _).symm : _)
      congr 1
      refine' Eq.trans _ (X.presheaf.map_comp _ _)
      change X.presheaf.map _ = _
      congr
      
    convert hP.holds_for_localization_away _ (X.presheaf.map (eq_to_hom U.1.open_embedding_obj_top).op r)
    · exact (RingHom.algebra_map_to_algebra _).symm
      
    · dsimp' [Scheme.Γ]
      have := U.2
      rw [← U.1.open_embedding_obj_top] at this
      convert is_localization_basic_open this _ using 6 <;>
        rw [opens.open_embedding_obj_top] <;> exact (Scheme.basic_open_res_eq _ _ _).symm
      
    
  · introv hs hs'
    exact source_affine_locally_of_source_open_cover_aux hP.respects_iso hP.2 _ _ _ hs hs'
    
  · rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_Union]
    exact ⟨⟨_, 𝒰.f x, rfl⟩, 𝒰.covers x⟩
    
  · rintro ⟨_, i, rfl⟩
    specialize H i
    rw [←
      hP.respects_iso.cancel_right_is_iso _
        (Scheme.Γ.map
          (is_open_immersion.iso_of_range_eq (𝒰.map i) (X.of_restrict (S i).1.OpenEmbedding)
                subtype.range_coe.symm).inv.op)] at
      H
    rwa [← Scheme.Γ.map_comp, ← op_comp, is_open_immersion.iso_of_range_eq_inv, is_open_immersion.lift_fac_assoc] at H
    

theorem affine_open_cover_tfae {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    Tfae
      [SourceAffineLocally (@P) f,
        ∃ (𝒰 : Scheme.OpenCover.{u} X)(_ : ∀ i, IsAffine (𝒰.obj i)), ∀ i : 𝒰.J, P (Scheme.Γ.map (𝒰.map i ≫ f).op),
        ∀ (𝒰 : Scheme.OpenCover.{u} X) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J), P (Scheme.Γ.map (𝒰.map i ≫ f).op),
        ∀ {U : Scheme} (g : U ⟶ X) [IsAffine U] [IsOpenImmersion g], P (Scheme.Γ.map (g ≫ f).op)] :=
  by
  tfae_have 1 → 4
  · intro H U g _ hg
    skip
    specialize H ⟨⟨_, hg.base_open.open_range⟩, range_is_affine_open_of_open_immersion g⟩
    rw [←
      hP.respects_iso.cancel_right_is_iso _
        (Scheme.Γ.map
          (is_open_immersion.iso_of_range_eq g (X.of_restrict (opens.open_embedding ⟨_, hg.base_open.open_range⟩))
                subtype.range_coe.symm).Hom.op),
      ← Scheme.Γ.map_comp, ← op_comp, is_open_immersion.iso_of_range_eq_hom] at H
    erw [is_open_immersion.lift_fac_assoc] at H
    exact H
    
  tfae_have 4 → 3
  · intro H 𝒰 _ i
    skip
    apply H
    
  tfae_have 3 → 2
  · intro H
    refine' ⟨X.affine_cover, inferInstance, H _⟩
    
  tfae_have 2 → 1
  · rintro ⟨𝒰, _, h𝒰⟩
    exact hP.source_affine_locally_of_source_open_cover f 𝒰 h𝒰
    
  tfae_finish

theorem open_cover_tfae {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    Tfae
      [SourceAffineLocally (@P) f, ∃ 𝒰 : Scheme.OpenCover.{u} X, ∀ i : 𝒰.J, SourceAffineLocally (@P) (𝒰.map i ≫ f),
        ∀ (𝒰 : Scheme.OpenCover.{u} X) (i : 𝒰.J), SourceAffineLocally (@P) (𝒰.map i ≫ f),
        ∀ {U : Scheme} (g : U ⟶ X) [IsOpenImmersion g], SourceAffineLocally (@P) (g ≫ f)] :=
  by
  tfae_have 1 → 4
  · intro H U g hg V
    skip
    rw [(hP.affine_open_cover_tfae f).out 0 3] at H
    haveI : is_affine _ := V.2
    rw [← category.assoc]
    apply H
    
  tfae_have 4 → 3
  · intro H 𝒰 _ i
    skip
    apply H
    
  tfae_have 3 → 2
  · intro H
    refine' ⟨X.affine_cover, H _⟩
    
  tfae_have 2 → 1
  · rintro ⟨𝒰, h𝒰⟩
    rw [(hP.affine_open_cover_tfae f).out 0 1]
    refine' ⟨𝒰.bind fun _ => Scheme.affine_cover _, _, _⟩
    · intro i
      dsimp'
      infer_instance
      
    · intro i
      specialize h𝒰 i.1
      rw [(hP.affine_open_cover_tfae (𝒰.map i.fst ≫ f)).out 0 3] at h𝒰
      erw [category.assoc]
      apply @h𝒰 _ (show _ from _)
      dsimp'
      infer_instance
      
    
  tfae_finish

theorem source_affine_locally_comp_of_is_open_immersion {X Y Z : Scheme.{u}} [IsAffine Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] (H : SourceAffineLocally (@P) g) : SourceAffineLocally (@P) (f ≫ g) := by
  apply ((hP.open_cover_tfae g).out 0 3).mp H

theorem source_affine_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (𝒰 : Scheme.OpenCover.{u} X)
    [∀ i, IsAffine (𝒰.obj i)] : SourceAffineLocally (@P) f ↔ ∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op) :=
  ⟨fun H =>
    let h := ((hP.affine_open_cover_tfae f).out 0 2).mp H
    h 𝒰,
    fun H =>
    let h := ((hP.affine_open_cover_tfae f).out 1 0).mp
    h ⟨𝒰, inferInstance, H⟩⟩

theorem is_local_source_affine_locally : (SourceAffineLocally @P).IsLocal :=
  source_affine_locally_is_local hP.RespectsIso hP.LocalizationPreserves
    (@RingHom.PropertyIsLocal.of_localization_span _ hP)

theorem is_local_affine_locally : PropertyIsLocalAtTarget (AffineLocally @P) :=
  hP.is_local_source_affine_locally.target_affine_locally_is_local

theorem affine_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{u} ((𝒰.pullbackCover f).obj i)) [∀ i j, IsAffine ((𝒰' i).obj j)] :
    AffineLocally (@P) f ↔ ∀ i j, P (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd).op) :=
  (hP.is_local_source_affine_locally.affine_open_cover_iff f 𝒰).trans
    (forall_congrₓ fun i => hP.source_affine_open_cover_iff _ (𝒰' i))

theorem source_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} X) :
    AffineLocally (@P) f ↔ ∀ i, AffineLocally (@P) (𝒰.map i ≫ f) := by
  constructor
  · intro H i U
    rw [morphism_restrict_comp]
    delta' morphism_restrict
    apply hP.source_affine_locally_comp_of_is_open_immersion
    apply H
    
  · intro H U
    haveI : is_affine _ := U.2
    apply ((hP.open_cover_tfae (f ∣_ U.1)).out 1 0).mp
    use 𝒰.pullback_cover (X.of_restrict _)
    intro i
    specialize H i U
    rw [morphism_restrict_comp] at H
    delta' morphism_restrict  at H
    have := source_affine_locally_respects_iso hP.respects_iso
    rw [category.assoc, affine_cancel_left_is_iso this, ← affine_cancel_left_is_iso this (pullback_symmetry _ _).Hom,
      pullback_symmetry_hom_comp_snd_assoc] at H
    exact H
    

theorem affine_locally_of_is_open_immersion (hP : RingHom.PropertyIsLocal @P) {X Y : Scheme} (f : X ⟶ Y)
    [hf : IsOpenImmersion f] : AffineLocally (@P) f := by
  intro U
  haveI H : is_affine _ := U.2
  rw [← category.comp_id (f ∣_ U)]
  apply hP.source_affine_locally_comp_of_is_open_immersion
  rw [hP.source_affine_open_cover_iff _ (Scheme.open_cover_of_is_iso (𝟙 _))]
  · intro i
    erw [category.id_comp, op_id, Scheme.Γ.map_id]
    convert hP.holds_for_localization_away _ (1 : Scheme.Γ.obj _)
    · exact (RingHom.algebra_map_to_algebra _).symm
      
    · infer_instance
      
    · refine' IsLocalization.away_of_is_unit_of_bijective _ is_unit_one Function.bijective_id
      
    
  · intro i
    exact H
    

theorem affine_locally_stable_under_composition : (AffineLocally @P).StableUnderComposition := by
  intro X Y S f g hf hg
  let 𝒰 : ∀ i, ((S.affine_cover.pullback_cover (f ≫ g)).obj i).OpenCover := by
    intro i
    refine' Scheme.open_cover.bind _ fun i => Scheme.affine_cover _
    apply Scheme.open_cover.pushforward_iso _ (pullback_right_pullback_fst_iso g (S.affine_cover.map i) f).Hom
    apply Scheme.pullback.open_cover_of_right
    exact (pullback g (S.affine_cover.map i)).affineCover
  rw [hP.affine_open_cover_iff (f ≫ g) S.affine_cover _]
  rotate_left
  · exact 𝒰
    
  · intro i j
    dsimp'  at *
    infer_instance
    
  · rintro i ⟨j, k⟩
    dsimp'  at i j k
    dsimp' only [Scheme.open_cover.bind_map, Scheme.open_cover.pushforward_iso_obj,
      Scheme.pullback.open_cover_of_right_obj, Scheme.open_cover.pushforward_iso_map,
      Scheme.pullback.open_cover_of_right_map, Scheme.open_cover.bind_obj]
    rw [category.assoc, category.assoc, pullback_right_pullback_fst_iso_hom_snd, pullback.lift_snd_assoc,
      category.assoc, ← category.assoc, op_comp, functor.map_comp]
    apply hP.stable_under_composition
    · exact (hP.affine_open_cover_iff _ _ _).mp hg _ _
      
    · delta' affine_locally  at hf
      rw [(hP.is_local_source_affine_locally.affine_open_cover_tfae f).out 0 3] at hf
      specialize hf ((pullback g (S.affine_cover.map i)).affineCover.map j ≫ pullback.fst)
      rw
        [(hP.affine_open_cover_tfae
              (pullback.snd :
                pullback f ((pullback g (S.affine_cover.map i)).affineCover.map j ≫ pullback.fst) ⟶ _)).out
          0 3] at
        hf
      apply hf
      
    

end RingHom.PropertyIsLocal

