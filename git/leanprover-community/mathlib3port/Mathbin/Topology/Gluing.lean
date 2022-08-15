/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.Topology.Category.Top.Default
import Mathbin.CategoryTheory.GlueData
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise

/-!
# Gluing Topological spaces

Given a family of gluing data (see `category_theory/glue_data`), we can then glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `Top.glue_data`: A structure containing the family of gluing data.
* `category_theory.glue_data.glued`: The glued topological space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `category_theory.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : ι`.
* `Top.glue_data.rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `t i j x = y`. See `Top.glue_data.ι_eq_iff_rel`.
* `Top.glue_data.mk`: A constructor of `glue_data` whose conditions are stated in terms of
  elements rather than subobjects and pullbacks.
* `Top.glue_data.of_open_subsets`: Given a family of open sets, we may glue them into a new
  topological space. This new space embeds into the original space, and is homeomorphic to it if
  the given family is an open cover (`Top.glue_data.open_cover_glue_homeo`).

## Main results

* `Top.glue_data.is_open_iff`: A set in `glued` is open iff its preimage along each `ι i` is
    open.
* `Top.glue_data.ι_jointly_surjective`: The `ι i`s are jointly surjective.
* `Top.glue_data.rel_equiv`: `rel` is an equivalence relation.
* `Top.glue_data.ι_eq_iff_rel`: `ι i x = ι j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `Top.glue_data.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `Top.glue_data.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `Top.glue_data.preimage_image_eq_preimage_f`: The preimage of the image of some `U ⊆ U i` is
    given by the preimage along `f j i`.
* `Top.glue_data.ι_open_embedding`: Each of the `ι i`s are open embeddings.

-/


noncomputable section

open TopologicalSpace CategoryTheory

universe v u

open CategoryTheory.Limits

namespace Top

/-- A family of gluing data consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
  (Note that this is `J × J → Top` rather than `J → J → Top` to connect to the
  limits library easier.)
4. An open embedding `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
    (This merely means that `V i j ∩ V i k ⊆ t i j ⁻¹' (V j i ∩ V j k)`.)
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the topological spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.

Most of the times it would be easier to use the constructor `Top.glue_data.mk'` where the conditions
are stated in a less categorical way.
-/
@[nolint has_nonempty_instance]
structure GlueData extends GlueData Top where
  f_open : ∀ i j, OpenEmbedding (f i j)
  f_mono := fun i j => (Top.mono_iff_injective _).mpr (f_open i j).toEmbedding.inj

namespace GlueData

variable (D : GlueData.{u})

-- mathport name: «expr𝖣»
local notation "𝖣" => D.toGlueData

theorem π_surjective : Function.Surjective 𝖣.π :=
  (Top.epi_iff_surjective 𝖣.π).mp inferInstance

theorem is_open_iff (U : Set 𝖣.glued) : IsOpen U ↔ ∀ i, IsOpen (𝖣.ι i ⁻¹' U) := by
  delta' CategoryTheory.GlueData.ι
  simp_rw [← multicoequalizer.ι_sigma_π 𝖣.diagram]
  rw [← (homeo_of_iso (multicoequalizer.iso_coequalizer 𝖣.diagram).symm).is_open_preimage]
  rw [coequalizer_is_open_iff, colimit_is_open_iff.{u}]
  constructor
  · intro h j
    exact h ⟨j⟩
    
  · intro h j
    cases j
    exact h j
    

theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : _)(y : D.U i), 𝖣.ι i y = x :=
  𝖣.ι_jointly_surjective (forget Top) x

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣 .ι i x = 𝖣 .ι j y`.
See `Top.glue_data.ι_eq_iff_rel`.
-/
def Rel (a b : Σi, ((D.U i : Top) : Type _)) : Prop :=
  a = b ∨ ∃ x : D.V (a.1, b.1), D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2

theorem rel_equiv : Equivalenceₓ D.Rel :=
  ⟨fun x => Or.inl (refl x), by
    rintro a b (⟨⟨⟩⟩ | ⟨x, e₁, e₂⟩)
    exacts[Or.inl rfl,
      Or.inr
        ⟨D.t _ _ x, by
          simp [← e₁, ← e₂]⟩],
    by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ (⟨⟨⟩⟩ | ⟨x, e₁, e₂⟩)
    exact id
    rintro (⟨⟨⟩⟩ | ⟨y, e₃, e₄⟩)
    exact Or.inr ⟨x, e₁, e₂⟩
    let z := (pullback_iso_prod_subtype (D.f j i) (D.f j k)).inv ⟨⟨_, _⟩, e₂.trans e₃.symm⟩
    have eq₁ : (D.t j i) ((pullback.fst : _ ⟶ D.V _) z) = x := by
      simp
    have eq₂ : (pullback.snd : _ ⟶ D.V _) z = y := pullback_iso_prod_subtype_inv_snd_apply _ _ _
    clear_value z
    right
    use (pullback.fst : _ ⟶ D.V (i, k)) (D.t' _ _ _ z)
    dsimp' only  at *
    substs e₁ e₃ e₄ eq₁ eq₂
    have h₁ : D.t' j i k ≫ pullback.fst ≫ D.f i k = pullback.fst ≫ D.t j i ≫ D.f i j := by
      rw [← 𝖣.t_fac_assoc]
      congr 1
      exact pullback.condition
    have h₂ : D.t' j i k ≫ pullback.fst ≫ D.t i k ≫ D.f k i = pullback.snd ≫ D.t j k ≫ D.f k j := by
      rw [← 𝖣.t_fac_assoc]
      apply @epi.left_cancellation _ _ _ _ (D.t' k j i)
      rw [𝖣.cocycle_assoc, 𝖣.t_fac_assoc, 𝖣.t_inv_assoc]
      exact pullback.condition.symm
    exact ⟨ContinuousMap.congr_fun h₁ z, ContinuousMap.congr_fun h₂ z⟩⟩

open CategoryTheory.Limits.WalkingParallelPair

theorem eqv_gen_of_π_eq {x y : ∐ D.U} (h : 𝖣.π x = 𝖣.π y) :
    EqvGen (Types.CoequalizerRel 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap) x y := by
  delta' glue_data.π multicoequalizer.sigma_π  at h
  simp_rw [comp_app] at h
  replace h := (Top.mono_iff_injective (multicoequalizer.iso_coequalizer 𝖣.diagram).inv).mp _ h
  let diagram := parallel_pair 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap ⋙ forget _
  have : colimit.ι diagram one x = colimit.ι diagram one y := by
    rw [← ι_preserves_colimits_iso_hom]
    simp [← h]
  have :
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).Hom) _ =
      (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.iso_colimit_cocone _).Hom) _ :=
    (congr_arg
      (colim.map (diagram_iso_parallel_pair diagram).Hom ≫
        (colimit.iso_colimit_cocone (types.coequalizer_colimit _ _)).Hom)
      this :
      _)
  simp only [← eq_to_hom_refl, ← types_comp_apply, ← colimit.ι_map_assoc, ← diagram_iso_parallel_pair_hom_app, ←
    colimit.iso_colimit_cocone_ι_hom, ← types_id_apply] at this
  exact Quot.eq.1 this
  infer_instance

theorem ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : D.U j) : 𝖣.ι i x = 𝖣.ι j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  constructor
  · delta' glue_data.ι
    simp_rw [← multicoequalizer.ι_sigma_π]
    intro h
    rw [← show _ = Sigma.mk i x from concrete_category.congr_hom (sigmaIsoSigma.{u} D.U).inv_hom_id _]
    rw [← show _ = Sigma.mk j y from concrete_category.congr_hom (sigmaIsoSigma.{u} D.U).inv_hom_id _]
    change InvImage D.rel (sigmaIsoSigma.{u} D.U).Hom _ _
    simp only [← Top.sigma_iso_sigma_inv_apply]
    rw [← (InvImage.equivalence _ _ D.rel_equiv).eqv_gen_iff]
    refine' EqvGen.mono _ (D.eqv_gen_of_π_eq h : _)
    rintro _ _ ⟨x⟩
    rw [← show (sigmaIsoSigma.{u} _).inv _ = x from concrete_category.congr_hom (sigmaIsoSigma.{u} _).hom_inv_id x]
    generalize (sigmaIsoSigma.{u} D.V).Hom x = x'
    obtain ⟨⟨i, j⟩, y⟩ := x'
    unfold InvImage multispan_index.fst_sigma_map multispan_index.snd_sigma_map
    simp only [← opens.inclusion_apply, ← Top.comp_app, ← sigma_iso_sigma_inv_apply, ←
      CategoryTheory.Limits.colimit.ι_desc_apply, ← cofan.mk_ι_app, ← sigma_iso_sigma_hom_ι_apply, ←
      ContinuousMap.to_fun_eq_coe]
    erw [sigma_iso_sigma_hom_ι_apply, sigma_iso_sigma_hom_ι_apply]
    exact
      Or.inr
        ⟨y, by
          dsimp' [← glue_data.diagram]
          simp ⟩
    
  · rintro (⟨⟨⟩⟩ | ⟨z, e₁, e₂⟩)
    rfl
    dsimp' only  at *
    subst e₁
    subst e₂
    simp
    

theorem ι_injective (i : D.J) : Function.Injective (𝖣.ι i) := by
  intro x y h
  rcases(D.ι_eq_iff_rel _ _ _ _).mp h with (⟨⟨⟩⟩ | ⟨_, e₁, e₂⟩)
  · rfl
    
  · dsimp' only  at *
    cases e₁
    cases e₂
    simp
    

instance ι_mono (i : D.J) : Mono (𝖣.ι i) :=
  (Top.mono_iff_injective _).mpr (D.ι_injective _)

theorem image_inter (i j : D.J) : Set.Range (𝖣.ι i) ∩ Set.Range (𝖣.ι j) = Set.Range (D.f i j ≫ 𝖣.ι _) := by
  ext x
  constructor
  · rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩
    obtain ⟨⟨⟩⟩ | ⟨y, e₁, e₂⟩ := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm)
    · exact
        ⟨inv (D.f i i) x₁, by
          simp [← eq₁]⟩
      
    · dsimp' only  at *
      substs e₁ eq₁
      exact
        ⟨y, by
          simp ⟩
      
    
  · rintro ⟨x, hx⟩
    exact
      ⟨⟨D.f i j x, hx⟩,
        ⟨D.f j i (D.t _ _ x), by
          simp [hx]⟩⟩
    

theorem preimage_range (i j : D.J) : 𝖣.ι j ⁻¹' Set.Range (𝖣.ι i) = Set.Range (D.f j i) := by
  rw [← Set.preimage_image_eq (Set.Range (D.f j i)) (D.ι_injective j), ← Set.image_univ, ← Set.image_univ, ←
    Set.image_comp, ← coe_comp, Set.image_univ, Set.image_univ, ← image_inter, Set.preimage_range_inter]

theorem preimage_image_eq_image (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' (𝖣.ι i '' U) = D.f _ _ '' ((D.t j i ≫ D.f _ _) ⁻¹' U) := by
  have : D.f _ _ ⁻¹' (𝖣.ι j ⁻¹' (𝖣.ι i '' U)) = (D.t j i ≫ D.f _ _) ⁻¹' U := by
    ext x
    conv_rhs => rw [← Set.preimage_image_eq U (D.ι_injective _)]
    generalize 𝖣.ι i '' U = U'
    simp
  rw [← this, Set.image_preimage_eq_inter_range]
  symm
  apply Set.inter_eq_self_of_subset_left
  rw [← D.preimage_range i j]
  exact Set.preimage_mono (Set.image_subset_range _ _)

theorem preimage_image_eq_image' (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' (𝖣.ι i '' U) = (D.t i j ≫ D.f _ _) '' (D.f _ _ ⁻¹' U) := by
  convert D.preimage_image_eq_image i j U using 1
  rw [coe_comp, coe_comp, ← Set.image_image]
  congr 1
  rw [← Set.eq_preimage_iff_image_eq, Set.preimage_preimage]
  change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _
  rw [𝖣.t_inv_assoc]
  rw [← is_iso_iff_bijective]
  apply (forget Top).map_is_iso

theorem open_image_open (i : D.J) (U : Opens (𝖣.U i)) : IsOpen (𝖣.ι i '' U) := by
  rw [is_open_iff]
  intro j
  rw [preimage_image_eq_image]
  apply (D.f_open _ _).IsOpenMap
  apply (D.t j i ≫ D.f i j).continuous_to_fun.is_open_preimage
  exact U.property

theorem ι_open_embedding (i : D.J) : OpenEmbedding (𝖣.ι i) :=
  open_embedding_of_continuous_injective_open (𝖣.ι i).continuous_to_fun (D.ι_injective i) fun U h =>
    D.open_image_open i ⟨U, h⟩

/-- A family of gluing data consists of
1. An index type `J`
2. A bundled topological space `U i` for each `i : J`.
3. An open set `V i j ⊆ U i` for each `i j : J`.
4. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `V i i = U i`.
7. `t i i` is the identity.
8. For each `x ∈ V i j ∩ V i k`, `t i j x ∈ V j k`.
9. `t j k (t i j x) = t i k x`.

We can then glue the topological spaces `U i` together by identifying `V i j` with `V j i`.
-/
@[nolint has_nonempty_instance]
structure MkCore where
  {J : Type u}
  U : J → Top.{u}
  V : ∀ i, J → Opens (U i)
  t : ∀ i j, (Opens.toTop _).obj (V i j) ⟶ (Opens.toTop _).obj (V j i)
  V_id : ∀ i, V i i = ⊤
  t_id : ∀ i, ⇑(t i i) = id
  t_inter : ∀ ⦃i j⦄ (k) (x : V i j), ↑x ∈ V i k → @coe (V j i) (U j) _ (t i j x) ∈ V j k
  cocycle :
    ∀ (i j k) (x : V i j) (h : ↑x ∈ V i k),
      @coe (V k j) (U k) _ (t j k ⟨↑(t i j x), t_inter k x h⟩) = @coe (V k i) (U k) _ (t i k ⟨x, h⟩)

theorem MkCore.t_inv (h : MkCore) (i j : h.J) (x : h.V j i) : h.t i j ((h.t j i) x) = x := by
  have := h.cocycle j i j x _
  rw [h.t_id] at this
  convert Subtype.eq this
  · ext
    rfl
    
  all_goals
    rw [h.V_id]
    trivial

instance (h : MkCore.{u}) (i j : h.J) : IsIso (h.t i j) := by
  use h.t j i
  constructor <;> ext1
  exacts[h.t_inv _ _ _, h.t_inv _ _ _]

/-- (Implementation) the restricted transition map to be fed into `glue_data`. -/
def MkCore.t' (h : MkCore.{u}) (i j k : h.J) :
    pullback (h.V i j).inclusion (h.V i k).inclusion ⟶ pullback (h.V j k).inclusion (h.V j i).inclusion := by
  refine' (pullback_iso_prod_subtype _ _).Hom ≫ ⟨_, _⟩ ≫ (pullback_iso_prod_subtype _ _).inv
  · intro x
    refine' ⟨⟨⟨(h.t i j x.1.1).1, _⟩, h.t i j x.1.1⟩, rfl⟩
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    exact h.t_inter _ ⟨x, hx⟩ hx'
    
  continuity

/-- This is a constructor of `Top.glue_data` whose arguments are in terms of elements and
intersections rather than subobjects and pullbacks. Please refer to `Top.glue_data.mk_core` for
details. -/
def mk' (h : MkCore.{u}) : Top.GlueData where
  J := h.J
  U := h.U
  V := fun i => (Opens.toTop _).obj (h.V i.1 i.2)
  f := fun i j => (h.V i j).inclusion
  f_id := fun i => (h.V_id i).symm ▸ IsIso.of_iso (Opens.inclusionTopIso (h.U i))
  f_open := fun i j : h.J => (h.V i j).OpenEmbedding
  t := h.t
  t_id := fun i => by
    ext
    rw [h.t_id]
    rfl
  t' := h.t'
  t_fac := fun i j k => by
    delta' mk_core.t'
    rw [category.assoc, category.assoc, pullback_iso_prod_subtype_inv_snd, ← iso.eq_inv_comp,
      pullback_iso_prod_subtype_inv_fst_assoc]
    ext ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    rfl
  cocycle := fun i j k => by
    delta' mk_core.t'
    simp_rw [← category.assoc]
    rw [iso.comp_inv_eq]
    simp only [← iso.inv_hom_id_assoc, ← category.assoc, ← category.id_comp]
    rw [← iso.eq_inv_comp, iso.inv_hom_id]
    ext1 ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    simp only [← Top.comp_app, ← ContinuousMap.coe_mk, ← Prod.mk.inj_iff, ← Top.id_app, ← Subtype.mk_eq_mk, ←
      Subtype.coe_mk]
    rw [← subtype.coe_injective.eq_iff, Subtype.val_eq_coe, Subtype.coe_mk, and_selfₓ]
    convert congr_arg coe (h.t_inv k i ⟨x, hx'⟩) using 3
    ext
    exact h.cocycle i j k ⟨x, hx⟩ hx'

variable {α : Type u} [TopologicalSpace α] {J : Type u} (U : J → Opens α)

include U

/-- We may construct a glue data from a family of open sets. -/
@[simps to_glue_data_J to_glue_data_U to_glue_data_V to_glue_data_t to_glue_data_f]
def ofOpenSubsets : Top.GlueData.{u} :=
  mk'.{u}
    { J, U := fun i => (opens.to_Top <| Top.of α).obj (U i), V := fun i j => (opens.map <| Opens.inclusion _).obj (U j),
      t := fun i j =>
        ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, by
          continuity⟩,
      V_id := fun i => by
        ext
        cases U i
        simp ,
      t_id := fun i => by
        ext
        rfl,
      t_inter := fun i j k x hx => hx, cocycle := fun i j k x h => rfl }

/-- The canonical map from the glue of a family of open subsets `α` into `α`.
This map is an open embedding (`from_open_subsets_glue_open_embedding`),
and its range is `⋃ i, (U i : set α)` (`range_from_open_subsets_glue`).
-/
def fromOpenSubsetsGlue : (ofOpenSubsets U).toGlueData.glued ⟶ Top.of α :=
  multicoequalizer.desc _ _ (fun x => Opens.inclusion _)
    (by
      rintro ⟨i, j⟩
      ext x
      rfl)

@[simp, elementwise]
theorem ι_from_open_subsets_glue (i : J) :
    (ofOpenSubsets U).toGlueData.ι i ≫ fromOpenSubsetsGlue U = Opens.inclusion _ :=
  multicoequalizer.π_desc _ _ _ _ _

theorem from_open_subsets_glue_injective : Function.Injective (fromOpenSubsetsGlue U) := by
  intro x y e
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective x
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective y
  rw [ι_from_open_subsets_glue_apply, ι_from_open_subsets_glue_apply] at e
  change x = y at e
  subst e
  rw [(of_open_subsets U).ι_eq_iff_rel]
  right
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩

theorem from_open_subsets_glue_is_open_map : IsOpenMap (fromOpenSubsetsGlue U) := by
  intro s hs
  rw [(of_open_subsets U).is_open_iff] at hs
  rw [is_open_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective x
  use from_open_subsets_glue U '' s ∩ Set.Range (@opens.inclusion (Top.of α) (U i))
  use Set.inter_subset_left _ _
  constructor
  · erw [← Set.image_preimage_eq_inter_range]
    apply (@opens.open_embedding (Top.of α) (U i)).IsOpenMap
    convert hs i using 1
    rw [← ι_from_open_subsets_glue, coe_comp, Set.preimage_comp]
    congr 1
    refine' Set.preimage_image_eq _ (from_open_subsets_glue_injective U)
    
  · refine' ⟨Set.mem_image_of_mem _ hx, _⟩
    rw [ι_from_open_subsets_glue_apply]
    exact Set.mem_range_self _
    

theorem from_open_subsets_glue_open_embedding : OpenEmbedding (fromOpenSubsetsGlue U) :=
  open_embedding_of_continuous_injective_open (ContinuousMap.continuous_to_fun _) (from_open_subsets_glue_injective U)
    (from_open_subsets_glue_is_open_map U)

theorem range_from_open_subsets_glue : Set.Range (fromOpenSubsetsGlue U) = ⋃ i, (U i : Set α) := by
  ext
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (of_open_subsets U).ι_jointly_surjective x
    rw [ι_from_open_subsets_glue_apply]
    exact Set.subset_Union _ i hx'
    
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    refine' ⟨(of_open_subsets U).toGlueData.ι i ⟨x, hx⟩, ι_from_open_subsets_glue_apply _ _ _⟩
    

/-- The gluing of an open cover is homeomomorphic to the original space. -/
def openCoverGlueHomeo (h : (⋃ i, (U i : Set α)) = Set.Univ) : (ofOpenSubsets U).toGlueData.glued ≃ₜ α :=
  Homeomorph.homeomorphOfContinuousOpen
    (Equivₓ.ofBijective (fromOpenSubsetsGlue U)
      ⟨from_open_subsets_glue_injective U, Set.range_iff_surjective.mp ((range_from_open_subsets_glue U).symm ▸ h)⟩)
    (fromOpenSubsetsGlue U).2 (from_open_subsets_glue_is_open_map U)

end GlueData

end Top

