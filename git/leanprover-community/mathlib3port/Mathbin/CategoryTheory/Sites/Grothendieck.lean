/-
Copyright (c) 2020 Bhavik Mehta, E. W. Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/
import Mathbin.CategoryTheory.Sites.Sieves
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathbin.CategoryTheory.Category.Preorder
import Mathbin.Order.Copy

/-!
# Grothendieck topologies

Definition and lemmas about Grothendieck topologies.
A Grothendieck topology for a category `C` is a set of sieves on each object `X` satisfying
certain closure conditions.

Alternate versions of the axioms (in arrow form) are also described.
Two explicit examples of Grothendieck topologies are given:
* The dense topology
* The atomic topology
as well as the complete lattice structure on Grothendieck topologies (which gives two additional
explicit topologies: the discrete and trivial topologies.)

A pretopology, or a basis for a topology is defined in `pretopology.lean`. The topology associated
to a topological space is defined in `spaces.lean`.

## Tags

Grothendieck topology, coverage, pretopology, site

## References

* [nLab, *Grothendieck topology*](https://ncatlab.org/nlab/show/Grothendieck+topology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## Implementation notes

We use the definition of [nlab] and [MM92][] (Chapter III, Section 2), where Grothendieck topologies
are saturated collections of morphisms, rather than the notions of the Stacks project (00VG) and
the Elephant, in which topologies are allowed to be unsaturated, and are then completed.
TODO (BM): Add the definition from Stacks, as a pretopology, and complete to a topology.

This is so that we can produce a bijective correspondence between Grothendieck topologies on a
small category and Lawvere-Tierney topologies on its presheaf topos, as well as the equivalence
between Grothendieck topoi and left exact reflective subcategories of presheaf toposes.
-/


universe w v u

namespace CategoryTheory

open CategoryTheory Category

variable (C : Type u) [Category.{v} C]

/-- The definition of a Grothendieck topology: a set of sieves `J X` on each object `X` satisfying
three axioms:
1. For every object `X`, the maximal sieve is in `J X`.
2. If `S ∈ J X` then its pullback along any `h : Y ⟶ X` is in `J Y`.
3. If `S ∈ J X` and `R` is a sieve on `X`, then provided that the pullback of `R` along any arrow
   `f : Y ⟶ X` in `S` is in `J Y`, we have that `R` itself is in `J X`.

A sieve `S` on `X` is referred to as `J`-covering, (or just covering), if `S ∈ J X`.

See <https://stacks.math.columbia.edu/tag/00Z4>, or [nlab], or [MM92][] Chapter III, Section 2,
Definition 1.
-/
structure GrothendieckTopology where
  Sieves : ∀ X : C, Set (Sieve X)
  top_mem' : ∀ X, ⊤ ∈ sieves X
  pullback_stable' : ∀ ⦃X Y : C⦄ ⦃S : Sieve X⦄ f : Y ⟶ X, S ∈ sieves X → S.pullback f ∈ sieves Y
  transitive' :
    ∀ ⦃X⦄ ⦃S : Sieve X⦄ hS : S ∈ sieves X R : Sieve X, (∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ sieves Y) → R ∈ sieves X

namespace GrothendieckTopology

instance : CoeFun (GrothendieckTopology C) fun _ => ∀ X : C, Set (Sieve X) :=
  ⟨Sieves⟩

variable {C} {X Y : C} {S R : Sieve X}

variable (J : GrothendieckTopology C)

/-- An extensionality lemma in terms of the coercion to a pi-type.
We prove this explicitly rather than deriving it so that it is in terms of the coercion rather than
the projection `.sieves`.
-/
@[ext]
theorem ext {J₁ J₂ : GrothendieckTopology C} (h : (J₁ : ∀ X : C, Set (Sieve X)) = J₂) : J₁ = J₂ := by
  cases J₁
  cases J₂
  congr
  apply h

@[simp]
theorem mem_sieves_iff_coe : S ∈ J.Sieves X ↔ S ∈ J X :=
  Iff.rfl

-- Also known as the maximality axiom.
@[simp]
theorem top_mem (X : C) : ⊤ ∈ J X :=
  J.top_mem' X

-- Also known as the stability axiom.
@[simp]
theorem pullback_stable (f : Y ⟶ X) (hS : S ∈ J X) : S.pullback f ∈ J Y :=
  J.pullback_stable' f hS

theorem transitive (hS : S ∈ J X) (R : Sieve X) (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → R.pullback f ∈ J Y) : R ∈ J X :=
  J.transitive' hS R h

theorem covering_of_eq_top : S = ⊤ → S ∈ J X := fun h => h.symm ▸ J.top_mem X

/-- If `S` is a subset of `R`, and `S` is covering, then `R` is covering as well.

See <https://stacks.math.columbia.edu/tag/00Z5> (2), or discussion after [MM92] Chapter III,
Section 2, Definition 1.
-/
theorem superset_covering (Hss : S ≤ R) (sjx : S ∈ J X) : R ∈ J X := by
  apply J.transitive sjx R fun Y f hf => _
  apply covering_of_eq_top
  rw [← top_le_iff, ← S.pullback_eq_top_of_mem hf]
  apply sieve.pullback_monotone _ Hss

/-- The intersection of two covering sieves is covering.

See <https://stacks.math.columbia.edu/tag/00Z5> (1), or [MM92] Chapter III,
Section 2, Definition 1 (iv).
-/
theorem intersection_covering (rj : R ∈ J X) (sj : S ∈ J X) : R⊓S ∈ J X := by
  apply J.transitive rj _ fun Y f Hf => _
  rw [sieve.pullback_inter, R.pullback_eq_top_of_mem Hf]
  simp [← sj]

@[simp]
theorem intersection_covering_iff : R⊓S ∈ J X ↔ R ∈ J X ∧ S ∈ J X :=
  ⟨fun h => ⟨J.superset_covering inf_le_left h, J.superset_covering inf_le_right h⟩, fun t =>
    intersection_covering _ t.1 t.2⟩

theorem bind_covering {S : Sieve X} {R : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → Sieve Y} (hS : S ∈ J X)
    (hR : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ H : S f, R H ∈ J Y) : Sieve.bind S R ∈ J X :=
  J.Transitive hS _ fun Y f hf => superset_covering J (Sieve.le_pullback_bind S R f hf) (hR hf)

/-- The sieve `S` on `X` `J`-covers an arrow `f` to `X` if `S.pullback f ∈ J Y`.
This definition is an alternate way of presenting a Grothendieck topology.
-/
def Covers (S : Sieve X) (f : Y ⟶ X) : Prop :=
  S.pullback f ∈ J Y

theorem covers_iff (S : Sieve X) (f : Y ⟶ X) : J.Covers S f ↔ S.pullback f ∈ J Y :=
  Iff.rfl

theorem covering_iff_covers_id (S : Sieve X) : S ∈ J X ↔ J.Covers S (𝟙 X) := by
  simp [← covers_iff]

/-- The maximality axiom in 'arrow' form: Any arrow `f` in `S` is covered by `S`. -/
theorem arrow_max (f : Y ⟶ X) (S : Sieve X) (hf : S f) : J.Covers S f := by
  rw [covers, (sieve.pullback_eq_top_iff_mem f).1 hf]
  apply J.top_mem

/-- The stability axiom in 'arrow' form: If `S` covers `f` then `S` covers `g ≫ f` for any `g`. -/
theorem arrow_stable (f : Y ⟶ X) (S : Sieve X) (h : J.Covers S f) {Z : C} (g : Z ⟶ Y) : J.Covers S (g ≫ f) := by
  rw [covers_iff] at h⊢
  simp [← h, ← sieve.pullback_comp]

/-- The transitivity axiom in 'arrow' form: If `S` covers `f` and every arrow in `S` is covered by
`R`, then `R` covers `f`.
-/
theorem arrow_trans (f : Y ⟶ X) (S R : Sieve X) (h : J.Covers S f) :
    (∀ {Z : C} g : Z ⟶ X, S g → J.Covers R g) → J.Covers R f := by
  intro k
  apply J.transitive h
  intro Z g hg
  rw [← sieve.pullback_comp]
  apply k (g ≫ f) hg

theorem arrow_intersect (f : Y ⟶ X) (S R : Sieve X) (hS : J.Covers S f) (hR : J.Covers R f) : J.Covers (S⊓R) f := by
  simpa [← covers_iff] using And.intro hS hR

variable (C)

/-- The trivial Grothendieck topology, in which only the maximal sieve is covering. This topology is
also known as the indiscrete, coarse, or chaotic topology.

See [MM92] Chapter III, Section 2, example (a), or
https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies
-/
def trivial : GrothendieckTopology C where
  Sieves := fun X => {⊤}
  top_mem' := fun X => rfl
  pullback_stable' := fun X Y S f hf => by
    rw [Set.mem_singleton_iff] at hf⊢
    simp [← hf]
  transitive' := fun X S hS R hR => by
    rw [Set.mem_singleton_iff, ← sieve.id_mem_iff_eq_top] at hS
    simpa using hR hS

/-- The discrete Grothendieck topology, in which every sieve is covering.

See https://en.wikipedia.org/wiki/Grothendieck_topology#The_discrete_and_indiscrete_topologies.
-/
def discrete : GrothendieckTopology C where
  Sieves := fun X => Set.Univ
  top_mem' := by
    simp
  pullback_stable' := fun X Y f => by
    simp
  transitive' := by
    simp

variable {C}

theorem trivial_covering : S ∈ trivial C X ↔ S = ⊤ :=
  Set.mem_singleton_iff

/-- See <https://stacks.math.columbia.edu/tag/00Z6> -/
instance :
    LE (GrothendieckTopology C) where le := fun J₁ J₂ => (J₁ : ∀ X : C, Set (Sieve X)) ≤ (J₂ : ∀ X : C, Set (Sieve X))

theorem le_def {J₁ J₂ : GrothendieckTopology C} : J₁ ≤ J₂ ↔ (J₁ : ∀ X : C, Set (Sieve X)) ≤ J₂ :=
  Iff.rfl

/-- See <https://stacks.math.columbia.edu/tag/00Z6> -/
instance : PartialOrderₓ (GrothendieckTopology C) :=
  { GrothendieckTopology.hasLe with le_refl := fun J₁ => le_def.mpr le_rfl,
    le_trans := fun J₁ J₂ J₃ h₁₂ h₂₃ => le_def.mpr (le_transₓ h₁₂ h₂₃),
    le_antisymm := fun J₁ J₂ h₁₂ h₂₁ => GrothendieckTopology.ext (le_antisymmₓ h₁₂ h₂₁) }

/-- See <https://stacks.math.columbia.edu/tag/00Z7> -/
instance :
    HasInfₓ (GrothendieckTopology C) where inf := fun T =>
    { Sieves := inf (sieves '' T),
      top_mem' := by
        rintro X S ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        simp ,
      pullback_stable' := by
        rintro X Y S hS f _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply J.pullback_stable _ (f _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩),
      transitive' := by
        rintro X S hS R h _ ⟨⟨_, J, hJ, rfl⟩, rfl⟩
        apply J.transitive (hS _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩) _ fun Y f hf => h hf _ ⟨⟨_, _, hJ, rfl⟩, rfl⟩ }

/-- See <https://stacks.math.columbia.edu/tag/00Z7> -/
theorem is_glb_Inf (s : Set (GrothendieckTopology C)) : IsGlb s (inf s) := by
  refine' @IsGlb.of_image _ _ _ _ sieves _ _ _ _
  · intros
    rfl
    
  · exact is_glb_Inf _
    

/-- Construct a complete lattice from the `Inf`, but make the trivial and discrete topologies
definitionally equal to the bottom and top respectively.
-/
instance : CompleteLattice (GrothendieckTopology C) :=
  CompleteLattice.copy (completeLatticeOfInf _ is_glb_Inf) _ rfl (discrete C)
    (by
      apply le_antisymmₓ
      · exact @CompleteLattice.le_top _ (completeLatticeOfInf _ is_glb_Inf) (discrete C)
        
      · intro X S hS
        apply Set.mem_univ
        )
    (trivial C)
    (by
      apply le_antisymmₓ
      · intro X S hS
        rw [trivial_covering] at hS
        apply covering_of_eq_top _ hS
        
      · refine' @CompleteLattice.bot_le _ (completeLatticeOfInf _ is_glb_Inf) (trivialₓ C)
        )
    _ rfl _ rfl _ rfl inf rfl

instance : Inhabited (GrothendieckTopology C) :=
  ⟨⊤⟩

@[simp]
theorem trivial_eq_bot : trivial C = ⊥ :=
  rfl

@[simp]
theorem discrete_eq_top : discrete C = ⊤ :=
  rfl

@[simp]
theorem bot_covering : S ∈ (⊥ : GrothendieckTopology C) X ↔ S = ⊤ :=
  trivial_covering

@[simp]
theorem top_covering : S ∈ (⊤ : GrothendieckTopology C) X :=
  ⟨⟩

theorem bot_covers (S : Sieve X) (f : Y ⟶ X) : (⊥ : GrothendieckTopology C).Covers S f ↔ S f := by
  rw [covers_iff, bot_covering, ← sieve.pullback_eq_top_iff_mem]

@[simp]
theorem top_covers (S : Sieve X) (f : Y ⟶ X) : (⊤ : GrothendieckTopology C).Covers S f := by
  simp [← covers_iff]

/-- The dense Grothendieck topology.

See https://ncatlab.org/nlab/show/dense+topology, or [MM92] Chapter III, Section 2, example (e).
-/
def dense : GrothendieckTopology C where
  Sieves := fun X S => ∀ {Y : C} f : Y ⟶ X, ∃ (Z : _)(g : Z ⟶ Y), S (g ≫ f)
  top_mem' := fun X Y f => ⟨Y, 𝟙 Y, ⟨⟩⟩
  pullback_stable' := by
    intro X Y S h H Z f
    rcases H (f ≫ h) with ⟨W, g, H'⟩
    exact
      ⟨W, g, by
        simpa⟩
  transitive' := by
    intro X S H₁ R H₂ Y f
    rcases H₁ f with ⟨Z, g, H₃⟩
    rcases H₂ H₃ (𝟙 Z) with ⟨W, h, H₄⟩
    exact
      ⟨W, h ≫ g, by
        simpa using H₄⟩

theorem dense_covering : S ∈ dense X ↔ ∀ {Y} f : Y ⟶ X, ∃ (Z : _)(g : Z ⟶ Y), S (g ≫ f) :=
  Iff.rfl

/-- A category satisfies the right Ore condition if any span can be completed to a commutative square.
NB. Any category with pullbacks obviously satisfies the right Ore condition, see
`right_ore_of_pullbacks`.
-/
def RightOreCondition (C : Type u) [Category.{v} C] : Prop :=
  ∀ {X Y Z : C} yx : Y ⟶ X zx : Z ⟶ X, ∃ (W : _)(wy : W ⟶ Y)(wz : W ⟶ Z), wy ≫ yx = wz ≫ zx

theorem right_ore_of_pullbacks [Limits.HasPullbacks C] : RightOreCondition C := fun X Y Z yx zx =>
  ⟨_, _, _, Limits.pullback.condition⟩

/-- The atomic Grothendieck topology: a sieve is covering iff it is nonempty.
For the pullback stability condition, we need the right Ore condition to hold.

See https://ncatlab.org/nlab/show/atomic+site, or [MM92] Chapter III, Section 2, example (f).
-/
def atomic (hro : RightOreCondition C) : GrothendieckTopology C where
  Sieves := fun X S => ∃ (Y : _)(f : Y ⟶ X), S f
  top_mem' := fun X => ⟨_, 𝟙 _, ⟨⟩⟩
  pullback_stable' := by
    rintro X Y S h ⟨Z, f, hf⟩
    rcases hro h f with ⟨W, g, k, comm⟩
    refine' ⟨_, g, _⟩
    simp [← comm, ← hf]
  transitive' := by
    rintro X S ⟨Y, f, hf⟩ R h
    rcases h hf with ⟨Z, g, hg⟩
    exact ⟨_, _, hg⟩

/-- `J.cover X` denotes the poset of covers of `X` with respect to the
Grothendieck topology `J`. -/
def Cover (X : C) :=
  { S : Sieve X // S ∈ J X }deriving Preorderₓ

namespace Cover

variable {J}

instance : Coe (J.cover X) (Sieve X) :=
  ⟨fun S => S.1⟩

instance : CoeFun (J.cover X) fun S => ∀ ⦃Y⦄ f : Y ⟶ X, Prop :=
  ⟨fun S Y f => (S : Sieve X) f⟩

@[simp]
theorem coe_fun_coe (S : J.cover X) (f : Y ⟶ X) : (S : Sieve X) f = S f :=
  rfl

theorem condition (S : J.cover X) : (S : Sieve X) ∈ J X :=
  S.2

@[ext]
theorem ext (S T : J.cover X) (h : ∀ ⦃Y⦄ f : Y ⟶ X, S f ↔ T f) : S = T :=
  Subtype.ext <| Sieve.ext h

instance : OrderTop (J.cover X) :=
  { (inferInstance : Preorderₓ _) with top := ⟨⊤, J.top_mem _⟩,
    le_top := fun S Y f h => by
      tauto }

instance : SemilatticeInf (J.cover X) :=
  { (inferInstance : Preorderₓ _) with inf := fun S T => ⟨S⊓T, J.intersection_covering S.condition T.condition⟩,
    le_antisymm := fun S T h1 h2 => (ext _ _) fun Y f => ⟨h1 _, h2 _⟩, inf_le_left := fun S T Y f hf => hf.1,
    inf_le_right := fun S T Y f hf => hf.2, le_inf := fun S T W h1 h2 Y f h => ⟨h1 _ h, h2 _ h⟩ }

instance : Inhabited (J.cover X) :=
  ⟨⊤⟩

/-- An auxiliary structure, used to define `S.index` in `plus.lean`. -/
@[nolint has_inhabited_instance, ext]
structure Arrow (S : J.cover X) where
  y : C
  f : Y ⟶ X
  hf : S f

/-- An auxiliary structure, used to define `S.index` in `plus.lean`. -/
@[nolint has_inhabited_instance, ext]
structure Relation (S : J.cover X) where
  (y₁ y₂ z : C)
  g₁ : Z ⟶ Y₁
  g₂ : Z ⟶ Y₂
  f₁ : Y₁ ⟶ X
  f₂ : Y₂ ⟶ X
  h₁ : S f₁
  h₂ : S f₂
  w : g₁ ≫ f₁ = g₂ ≫ f₂

/-- Map a `arrow` along a refinement `S ⟶ T`. -/
@[simps]
def Arrow.map {S T : J.cover X} (I : S.arrow) (f : S ⟶ T) : T.arrow :=
  ⟨I.y, I.f, f.le _ I.hf⟩

/-- Map a `relation` along a refinement `S ⟶ T`. -/
@[simps]
def Relation.map {S T : J.cover X} (I : S.Relation) (f : S ⟶ T) : T.Relation :=
  ⟨_, _, _, I.g₁, I.g₂, I.f₁, I.f₂, f.le _ I.h₁, f.le _ I.h₂, I.w⟩

/-- The first `arrow` associated to a `relation`.
Used in defining `index` in `plus.lean`. -/
@[simps]
def Relation.fst {S : J.cover X} (I : S.Relation) : S.arrow :=
  ⟨I.y₁, I.f₁, I.h₁⟩

/-- The second `arrow` associated to a `relation`.
Used in defining `index` in `plus.lean`. -/
@[simps]
def Relation.snd {S : J.cover X} (I : S.Relation) : S.arrow :=
  ⟨I.y₂, I.f₂, I.h₂⟩

@[simp]
theorem Relation.map_fst {S T : J.cover X} (I : S.Relation) (f : S ⟶ T) : I.fst.map f = (I.map f).fst :=
  rfl

@[simp]
theorem Relation.map_snd {S T : J.cover X} (I : S.Relation) (f : S ⟶ T) : I.snd.map f = (I.map f).snd :=
  rfl

/-- Pull back a cover along a morphism. -/
def pullback (S : J.cover X) (f : Y ⟶ X) : J.cover Y :=
  ⟨Sieve.pullback f S, J.pullback_stable _ S.condition⟩

/-- An arrow of `S.pullback f` gives rise to an arrow of `S`. -/
@[simps]
def Arrow.base {f : Y ⟶ X} {S : J.cover X} (I : (S.pullback f).arrow) : S.arrow :=
  ⟨I.y, I.f ≫ f, I.hf⟩

/-- A relation of `S.pullback f` gives rise to a relation of `S`. -/
@[simps]
def Relation.base {f : Y ⟶ X} {S : J.cover X} (I : (S.pullback f).Relation) : S.Relation :=
  ⟨_, _, _, I.g₁, I.g₂, I.f₁ ≫ f, I.f₂ ≫ f, I.h₁, I.h₂, by
    simp [← reassoc_of I.w]⟩

@[simp]
theorem Relation.base_fst {f : Y ⟶ X} {S : J.cover X} (I : (S.pullback f).Relation) : I.fst.base = I.base.fst :=
  rfl

@[simp]
theorem Relation.base_snd {f : Y ⟶ X} {S : J.cover X} (I : (S.pullback f).Relation) : I.snd.base = I.base.snd :=
  rfl

@[simp]
theorem coe_pullback {Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (S : J.cover X) : (S.pullback f) g ↔ S (g ≫ f) :=
  Iff.rfl

/-- The isomorphism between `S` and the pullback of `S` w.r.t. the identity. -/
def pullbackId (S : J.cover X) : S.pullback (𝟙 X) ≅ S :=
  eq_to_iso <|
    (Cover.ext _ _) fun Y f => by
      simp

/-- Pulling back with respect to a composition is the composition of the pullbacks. -/
def pullbackComp {X Y Z : C} (S : J.cover X) (f : Z ⟶ Y) (g : Y ⟶ X) : S.pullback (f ≫ g) ≅ (S.pullback g).pullback f :=
  eq_to_iso <|
    (Cover.ext _ _) fun Y f => by
      simp

/-- Combine a family of covers over a cover. -/
def bind {X : C} (S : J.cover X) (T : ∀ I : S.arrow, J.cover I.y) : J.cover X :=
  ⟨Sieve.bind S fun Y f hf => T ⟨Y, f, hf⟩, J.bind_covering S.condition fun _ _ _ => (T _).condition⟩

/-- The canonical moprhism from `S.bind T` to `T`. -/
def bindToBase {X : C} (S : J.cover X) (T : ∀ I : S.arrow, J.cover I.y) : S.bind T ⟶ S :=
  hom_of_le <| by
    rintro Y f ⟨Z, e1, e2, h1, h2, h3⟩
    rw [← h3]
    apply sieve.downward_closed
    exact h1

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the object `B`. -/
noncomputable def Arrow.middle {X : C} {S : J.cover X} {T : ∀ I : S.arrow, J.cover I.y} (I : (S.bind T).arrow) : C :=
  I.hf.some

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`. -/
noncomputable def Arrow.toMiddleHom {X : C} {S : J.cover X} {T : ∀ I : S.arrow, J.cover I.y} (I : (S.bind T).arrow) :
    I.y ⟶ I.middle :=
  I.hf.some_spec.some

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`. -/
noncomputable def Arrow.fromMiddleHom {X : C} {S : J.cover X} {T : ∀ I : S.arrow, J.cover I.y} (I : (S.bind T).arrow) :
    I.middle ⟶ X :=
  I.hf.some_spec.some_spec.some

theorem Arrow.from_middle_condition {X : C} {S : J.cover X} {T : ∀ I : S.arrow, J.cover I.y} (I : (S.bind T).arrow) :
    S I.fromMiddleHom :=
  I.hf.some_spec.some_spec.some_spec.some

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `B ⟶ X`, as an arrow. -/
noncomputable def Arrow.fromMiddle {X : C} {S : J.cover X} {T : ∀ I : S.arrow, J.cover I.y} (I : (S.bind T).arrow) :
    S.arrow :=
  ⟨_, I.fromMiddleHom, I.from_middle_condition⟩

theorem Arrow.to_middle_condition {X : C} {S : J.cover X} {T : ∀ I : S.arrow, J.cover I.y} (I : (S.bind T).arrow) :
    (T I.fromMiddle) I.toMiddleHom :=
  I.hf.some_spec.some_spec.some_spec.some_spec.1

/-- An arrow in bind has the form `A ⟶ B ⟶ X` where `A ⟶ B` is an arrow in `T I` for some `I`.
 and `B ⟶ X` is an arrow of `S`. This is the hom `A ⟶ B`, as an arrow. -/
noncomputable def Arrow.toMiddle {X : C} {S : J.cover X} {T : ∀ I : S.arrow, J.cover I.y} (I : (S.bind T).arrow) :
    (T I.fromMiddle).arrow :=
  ⟨_, I.toMiddleHom, I.to_middle_condition⟩

theorem Arrow.middle_spec {X : C} {S : J.cover X} {T : ∀ I : S.arrow, J.cover I.y} (I : (S.bind T).arrow) :
    I.toMiddleHom ≫ I.fromMiddleHom = I.f :=
  I.hf.some_spec.some_spec.some_spec.some_spec.2

/-- To every `S : J.cover X` and presheaf `P`, associate a `multicospan_index`. -/
-- This is used extensively in `plus.lean`, etc.
-- We place this definition here as it will be used in `sheaf.lean` as well.
def index {D : Type w} [Category.{max v u} D] (S : J.cover X) (P : Cᵒᵖ ⥤ D) : Limits.MulticospanIndex D where
  L := S.arrow
  R := S.Relation
  fstTo := fun I => I.fst
  sndTo := fun I => I.snd
  left := fun I => P.obj (Opposite.op I.y)
  right := fun I => P.obj (Opposite.op I.z)
  fst := fun I => P.map I.g₁.op
  snd := fun I => P.map I.g₂.op

/-- The natural multifork associated to `S : J.cover X` for a presheaf `P`.
Saying that this multifork is a limit is essentially equivalent to the sheaf condition at the
given object for the given covering sieve. See `sheaf.lean` for an equivalent sheaf condition
using this.
-/
abbrev multifork {D : Type w} [Category.{max v u} D] (S : J.cover X) (P : Cᵒᵖ ⥤ D) : Limits.Multifork (S.index P) :=
  Limits.Multifork.ofι _ (P.obj (Opposite.op X)) (fun I => P.map I.f.op)
    (by
      intro I
      dsimp' [← index]
      simp only [P.map_comp, op_comp, ← I.w])

/-- The canonical map from `P.obj (op X)` to the multiequalizer associated to a covering sieve,
assuming such a multiequalizer exists. This will be used in `sheaf.lean` to provide an equivalent
sheaf condition in terms of multiequalizers. -/
noncomputable abbrev toMultiequalizer {D : Type w} [Category.{max v u} D] (S : J.cover X) (P : Cᵒᵖ ⥤ D)
    [Limits.HasMultiequalizer (S.index P)] : P.obj (Opposite.op X) ⟶ Limits.multiequalizer (S.index P) :=
  Limits.multiequalizer.lift _ _ (fun I => P.map I.f.op)
    (by
      intro I
      dsimp' only [← index, ← relation.fst, ← relation.snd]
      simp only [P.map_comp, op_comp, ← I.w])

end Cover

/-- Pull back a cover along a morphism. -/
@[simps obj]
def pullback (f : Y ⟶ X) : J.cover X ⥤ J.cover Y where
  obj := fun S => S.pullback f
  map := fun S T f => (Sieve.pullback_monotone _ f.le).Hom

/-- Pulling back along the identity is naturally isomorphic to the identity functor. -/
def pullbackId (X : C) : J.pullback (𝟙 X) ≅ 𝟭 _ :=
  (NatIso.ofComponents fun S => S.pullback_id) <| by
    tidy

/-- Pulling back along a composition is naturally isomorphic to
the composition of the pullbacks. -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : J.pullback (f ≫ g) ≅ J.pullback g ⋙ J.pullback f :=
  (NatIso.ofComponents fun S => S.pullback_comp f g) <| by
    tidy

end GrothendieckTopology

end CategoryTheory

