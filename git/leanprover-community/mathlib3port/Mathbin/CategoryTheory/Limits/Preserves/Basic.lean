/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Reid Barton, Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# Preservation and reflection of (co)limits.

There are various distinct notions of "preserving limits". The one we
aim to capture here is: A functor F : C → D "preserves limits" if it
sends every limit cone in C to a limit cone in D. Informally, F
preserves all the limits which exist in C.

Note that:

* Of course, we do not want to require F to *strictly* take chosen
  limit cones of C to chosen limit cones of D. Indeed, the above
  definition makes no reference to a choice of limit cones so it makes
  sense without any conditions on C or D.

* Some diagrams in C may have no limit. In this case, there is no
  condition on the behavior of F on such diagrams. There are other
  notions (such as "flat functor") which impose conditions also on
  diagrams in C with no limits, but these are not considered here.

In order to be able to express the property of preserving limits of a
certain form, we say that a functor F preserves the limit of a
diagram K if F sends every limit cone on K to a limit cone. This is
vacuously satisfied when K does not admit a limit, which is consistent
with the above definition of "preserves limits".
-/


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

-- morphism levels before object levels. See note [category_theory universes].
universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

/-- A functor `F` preserves limits of `K` (written as `preserves_limit K F`)
if `F` maps any limit cone over `K` to a limit cone.
-/
class PreservesLimit (K : J ⥤ C) (F : C ⥤ D) where
  preserves : ∀ {c : Cone K}, IsLimit c → IsLimit (F.mapCone c)

/-- A functor `F` preserves colimits of `K` (written as `preserves_colimit K F`)
if `F` maps any colimit cocone over `K` to a colimit cocone.
-/
class PreservesColimit (K : J ⥤ C) (F : C ⥤ D) where
  preserves : ∀ {c : Cocone K}, IsColimit c → IsColimit (F.mapCocone c)

/-- We say that `F` preserves limits of shape `J` if `F` preserves limits for every diagram
    `K : J ⥤ C`, i.e., `F` maps limit cones over `K` to limit cones. -/
class PreservesLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  PreservesLimit : ∀ {K : J ⥤ C}, PreservesLimit K F := by
    run_tac
      tactic.apply_instance

/-- We say that `F` preserves colimits of shape `J` if `F` preserves colimits for every diagram
    `K : J ⥤ C`, i.e., `F` maps colimit cocones over `K` to colimit cocones. -/
class PreservesColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  PreservesColimit : ∀ {K : J ⥤ C}, PreservesColimit K F := by
    run_tac
      tactic.apply_instance

/-- `preserves_limits_of_size.{v u} F` means that `F` sends all limit cones over any
diagram `J ⥤ C` to limit cones, where `J : Type u` with `[category.{v} J]`. -/
-- This should be used with explicit universe variables.
@[nolint check_univs]
class PreservesLimitsOfSize (F : C ⥤ D) where
  PreservesLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], PreservesLimitsOfShape J F := by
    run_tac
      tactic.apply_instance

/-- We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones. -/
abbrev PreservesLimits (F : C ⥤ D) :=
  PreservesLimitsOfSize.{v₂, v₂} F

/-- `preserves_colimits_of_size.{v u} F` means that `F` sends all colimit cocones over any
diagram `J ⥤ C` to colimit cocones, where `J : Type u` with `[category.{v} J]`. -/
-- This should be used with explicit universe variables.
@[nolint check_univs]
class PreservesColimitsOfSize (F : C ⥤ D) where
  PreservesColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], PreservesColimitsOfShape J F := by
    run_tac
      tactic.apply_instance

/-- We say that `F` preserves (small) limits if it sends small
limit cones over any diagram to limit cones. -/
abbrev PreservesColimits (F : C ⥤ D) :=
  PreservesColimitsOfSize.{v₂, v₂} F

attribute [instance]
  preserves_limits_of_shape.preserves_limit preserves_limits_of_size.preserves_limits_of_shape preserves_colimits_of_shape.preserves_colimit preserves_colimits_of_size.preserves_colimits_of_shape

/-- A convenience function for `preserves_limit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
-- see Note [lower instance priority]
def isLimitOfPreserves (F : C ⥤ D) {c : Cone K} (t : IsLimit c) [PreservesLimit K F] : IsLimit (F.mapCone c) :=
  PreservesLimit.preserves t

/-- A convenience function for `preserves_colimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isColimitOfPreserves (F : C ⥤ D) {c : Cocone K} (t : IsColimit c) [PreservesColimit K F] :
    IsColimit (F.mapCocone c) :=
  PreservesColimit.preserves t

instance preserves_limit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (PreservesLimit K F) := by
  constructor <;> rintro ⟨a⟩ ⟨b⟩ <;> congr

instance preserves_colimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (PreservesColimit K F) := by
  constructor <;> rintro ⟨a⟩ ⟨b⟩ <;> congr

instance preserves_limits_of_shape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesLimitsOfShape J F) := by
  constructor
  intros
  cases a
  cases b
  congr

instance preserves_colimits_of_shape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (PreservesColimitsOfShape J F) := by
  constructor
  intros
  cases a
  cases b
  congr

instance preserves_limits_subsingleton (F : C ⥤ D) : Subsingleton (PreservesLimitsOfSize.{w', w} F) := by
  constructor
  intros
  cases a
  cases b
  cc

instance preserves_colimits_subsingleton (F : C ⥤ D) : Subsingleton (PreservesColimitsOfSize.{w', w} F) := by
  constructor
  intros
  cases a
  cases b
  cc

instance idPreservesLimits : PreservesLimitsOfSize.{w', w} (𝟭 C) where
  PreservesLimitsOfShape := fun J 𝒥 =>
    { PreservesLimit := fun K =>
        ⟨fun c h =>
          ⟨fun s => h.lift ⟨s.x, fun j => s.π.app j, fun j j' f => s.π.naturality f⟩, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s m w <;> rcases s with ⟨_, _, _⟩ <;> exact h.uniq _ m w⟩⟩ }

instance idPreservesColimits : PreservesColimitsOfSize.{w', w} (𝟭 C) where
  PreservesColimitsOfShape := fun J 𝒥 =>
    { PreservesColimit := fun K =>
        ⟨fun c h =>
          ⟨fun s => h.desc ⟨s.x, fun j => s.ι.app j, fun j j' f => s.ι.naturality f⟩, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s m w <;> rcases s with ⟨_, _, _⟩ <;> exact h.uniq _ m w⟩⟩ }

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]

variable (F : C ⥤ D) (G : D ⥤ E)

attribute [local elabWithoutExpectedType] preserves_limit.preserves preserves_colimit.preserves

instance compPreservesLimit [PreservesLimit K F] [PreservesLimit (K ⋙ F) G] : PreservesLimit K (F ⋙ G) :=
  ⟨fun c h => PreservesLimit.preserves (PreservesLimit.preserves h)⟩

instance compPreservesLimitsOfShape [PreservesLimitsOfShape J F] [PreservesLimitsOfShape J G] :
    PreservesLimitsOfShape J (F ⋙ G) :=
  {  }

instance compPreservesLimits [PreservesLimitsOfSize.{w', w} F] [PreservesLimitsOfSize.{w', w} G] :
    PreservesLimitsOfSize.{w', w} (F ⋙ G) :=
  {  }

instance compPreservesColimit [PreservesColimit K F] [PreservesColimit (K ⋙ F) G] : PreservesColimit K (F ⋙ G) :=
  ⟨fun c h => PreservesColimit.preserves (PreservesColimit.preserves h)⟩

instance compPreservesColimitsOfShape [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G] :
    PreservesColimitsOfShape J (F ⋙ G) :=
  {  }

instance compPreservesColimits [PreservesColimitsOfSize.{w', w} F] [PreservesColimitsOfSize.{w', w} G] :
    PreservesColimitsOfSize.{w', w} (F ⋙ G) :=
  {  }

end

/-- If F preserves one limit cone for the diagram K,
  then it preserves any limit cone for K. -/
def preservesLimitOfPreservesLimitCone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLimit (F.mapCone t)) :
    PreservesLimit K F :=
  ⟨fun t' h' => IsLimit.ofIsoLimit hF (Functor.mapIso _ (IsLimit.uniqueUpToIso h h'))⟩

/-- Transfer preservation of limits along a natural isomorphism in the diagram. -/
def preservesLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] :
    PreservesLimit K₂ F where
  preserves := fun c t => by
    apply is_limit.postcompose_inv_equiv (iso_whisker_right h F : _) _ _
    have := (is_limit.postcompose_inv_equiv h c).symm t
    apply is_limit.of_iso_limit (is_limit_of_preserves F this)
    refine'
      cones.ext (iso.refl _) fun j => by
        tidy

/-- Transfer preservation of a limit along a natural isomorphism in the functor. -/
def preservesLimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesLimit K F] : PreservesLimit K G where
  preserves := fun c t => IsLimit.mapConeEquiv h (PreservesLimit.preserves t)

/-- Transfer preservation of limits of shape along a natural isomorphism in the functor. -/
def preservesLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] :
    PreservesLimitsOfShape J G where
  PreservesLimit := fun K => preservesLimitOfNatIso K h

/-- Transfer preservation of limits along a natural isomorphism in the functor. -/
def preservesLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] :
    PreservesLimitsOfSize.{w, w'} G where
  PreservesLimitsOfShape := fun J 𝒥₁ => preserves_limits_of_shape_of_nat_iso h

/-- Transfer preservation of limits along a equivalence in the shape. -/
def preservesLimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J' F where
  PreservesLimit := fun K =>
    { preserves := fun c t => by
        let equ := e.inv_fun_id_assoc (K ⋙ F)
        have := (is_limit_of_preserves F (t.whisker_equivalence e)).whiskerEquivalence e.symm
        apply ((is_limit.postcompose_hom_equiv equ _).symm this).ofIsoLimit
        refine' cones.ext (iso.refl _) fun j => _
        · dsimp'
          simp [← functor.map_comp]
           }

/-- If F preserves one colimit cocone for the diagram K,
  then it preserves any colimit cocone for K. -/
-- See library note [dsimp, simp].
def preservesColimitOfPreservesColimitCocone {F : C ⥤ D} {t : Cocone K} (h : IsColimit t)
    (hF : IsColimit (F.mapCocone t)) : PreservesColimit K F :=
  ⟨fun t' h' => IsColimit.ofIsoColimit hF (Functor.mapIso _ (IsColimit.uniqueUpToIso h h'))⟩

/-- Transfer preservation of colimits along a natural isomorphism in the shape. -/
def preservesColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F] :
    PreservesColimit K₂ F where
  preserves := fun c t => by
    apply is_colimit.precompose_hom_equiv (iso_whisker_right h F : _) _ _
    have := (is_colimit.precompose_hom_equiv h c).symm t
    apply is_colimit.of_iso_colimit (is_colimit_of_preserves F this)
    refine'
      cocones.ext (iso.refl _) fun j => by
        tidy

/-- Transfer preservation of a colimit along a natural isomorphism in the functor. -/
def preservesColimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [PreservesColimit K F] : PreservesColimit K G where
  preserves := fun c t => IsColimit.mapCoconeEquiv h (PreservesColimit.preserves t)

/-- Transfer preservation of colimits of shape along a natural isomorphism in the functor. -/
def preservesColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J G where
  PreservesColimit := fun K => preservesColimitOfNatIso K h

/-- Transfer preservation of colimits along a natural isomorphism in the functor. -/
def preservesColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] :
    PreservesColimitsOfSize.{w, w'} G where
  PreservesColimitsOfShape := fun J 𝒥₁ => preserves_colimits_of_shape_of_nat_iso h

/-- Transfer preservation of colimits along a equivalence in the shape. -/
def preservesColimitsOfShapeOfEquiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J' F where
  PreservesColimit := fun K =>
    { preserves := fun c t => by
        let equ := e.inv_fun_id_assoc (K ⋙ F)
        have := (is_colimit_of_preserves F (t.whisker_equivalence e)).whiskerEquivalence e.symm
        apply ((is_colimit.precompose_inv_equiv equ _).symm this).ofIsoColimit
        refine' cocones.ext (iso.refl _) fun j => _
        · dsimp'
          simp [← functor.map_comp]
           }

/-- A functor `F : C ⥤ D` reflects limits for `K : J ⥤ C` if
whenever the image of a cone over `K` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
-- See library note [dsimp, simp].
class ReflectsLimit (K : J ⥤ C) (F : C ⥤ D) where
  reflects : ∀ {c : Cone K}, IsLimit (F.mapCone c) → IsLimit c

/-- A functor `F : C ⥤ D` reflects colimits for `K : J ⥤ C` if
whenever the image of a cocone over `K` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class ReflectsColimit (K : J ⥤ C) (F : C ⥤ D) where
  reflects : ∀ {c : Cocone K}, IsColimit (F.mapCocone c) → IsColimit c

/-- A functor `F : C ⥤ D` reflects limits of shape `J` if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class ReflectsLimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  ReflectsLimit : ∀ {K : J ⥤ C}, ReflectsLimit K F := by
    run_tac
      tactic.apply_instance

/-- A functor `F : C ⥤ D` reflects colimits of shape `J` if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class ReflectsColimitsOfShape (J : Type w) [Category.{w'} J] (F : C ⥤ D) where
  ReflectsColimit : ∀ {K : J ⥤ C}, ReflectsColimit K F := by
    run_tac
      tactic.apply_instance

/-- A functor `F : C ⥤ D` reflects limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
-- This should be used with explicit universe variables.
@[nolint check_univs]
class ReflectsLimitsOfSize (F : C ⥤ D) where
  ReflectsLimitsOfShape : ∀ {J : Type w} [Category.{w'} J], ReflectsLimitsOfShape J F := by
    run_tac
      tactic.apply_instance

/-- A functor `F : C ⥤ D` reflects (small) limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
abbrev ReflectsLimits (F : C ⥤ D) :=
  ReflectsLimitsOfSize.{v₂, v₂} F

/-- A functor `F : C ⥤ D` reflects colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
-- This should be used with explicit universe variables.
@[nolint check_univs]
class ReflectsColimitsOfSize (F : C ⥤ D) where
  ReflectsColimitsOfShape : ∀ {J : Type w} [Category.{w'} J], ReflectsColimitsOfShape J F := by
    run_tac
      tactic.apply_instance

/-- A functor `F : C ⥤ D` reflects (small) colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
abbrev ReflectsColimits (F : C ⥤ D) :=
  ReflectsColimitsOfSize.{v₂, v₂} F

/-- A convenience function for `reflects_limit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isLimitOfReflects (F : C ⥤ D) {c : Cone K} (t : IsLimit (F.mapCone c)) [ReflectsLimit K F] : IsLimit c :=
  ReflectsLimit.reflects t

/-- A convenience function for `reflects_colimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isColimitOfReflects (F : C ⥤ D) {c : Cocone K} (t : IsColimit (F.mapCocone c)) [ReflectsColimit K F] :
    IsColimit c :=
  ReflectsColimit.reflects t

instance reflects_limit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (ReflectsLimit K F) := by
  constructor <;> rintro ⟨a⟩ ⟨b⟩ <;> congr

instance reflects_colimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (ReflectsColimit K F) := by
  constructor <;> rintro ⟨a⟩ ⟨b⟩ <;> congr

instance reflects_limits_of_shape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsLimitsOfShape J F) := by
  constructor
  intros
  cases a
  cases b
  congr

instance reflects_colimits_of_shape_subsingleton (J : Type w) [Category.{w'} J] (F : C ⥤ D) :
    Subsingleton (ReflectsColimitsOfShape J F) := by
  constructor
  intros
  cases a
  cases b
  congr

instance reflects_limits_subsingleton (F : C ⥤ D) : Subsingleton (ReflectsLimitsOfSize.{w', w} F) := by
  constructor
  intros
  cases a
  cases b
  cc

instance reflects_colimits_subsingleton (F : C ⥤ D) : Subsingleton (ReflectsColimitsOfSize.{w', w} F) := by
  constructor
  intros
  cases a
  cases b
  cc

-- see Note [lower instance priority]
instance (priority := 100) reflectsLimitOfReflectsLimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [H : ReflectsLimitsOfShape J F] : ReflectsLimit K F :=
  reflects_limits_of_shape.reflects_limit

-- see Note [lower instance priority]
instance (priority := 100) reflectsColimitOfReflectsColimitsOfShape (K : J ⥤ C) (F : C ⥤ D)
    [H : ReflectsColimitsOfShape J F] : ReflectsColimit K F :=
  reflects_colimits_of_shape.reflects_colimit

-- see Note [lower instance priority]
instance (priority := 100) reflectsLimitsOfShapeOfReflectsLimits (J : Type w) [Category.{w'} J] (F : C ⥤ D)
    [H : ReflectsLimitsOfSize.{w', w} F] : ReflectsLimitsOfShape J F :=
  reflects_limits_of_size.reflects_limits_of_shape

-- see Note [lower instance priority]
instance (priority := 100) reflectsColimitsOfShapeOfReflectsColimits (J : Type w) [Category.{w'} J] (F : C ⥤ D)
    [H : ReflectsColimitsOfSize.{w', w} F] : ReflectsColimitsOfShape J F :=
  reflects_colimits_of_size.reflects_colimits_of_shape

instance idReflectsLimits : ReflectsLimitsOfSize.{w, w'} (𝟭 C) where
  ReflectsLimitsOfShape := fun J 𝒥 =>
    { ReflectsLimit := fun K =>
        ⟨fun c h =>
          ⟨fun s => h.lift ⟨s.x, fun j => s.π.app j, fun j j' f => s.π.naturality f⟩, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s m w <;> rcases s with ⟨_, _, _⟩ <;> exact h.uniq _ m w⟩⟩ }

instance idReflectsColimits : ReflectsColimitsOfSize.{w, w'} (𝟭 C) where
  ReflectsColimitsOfShape := fun J 𝒥 =>
    { ReflectsColimit := fun K =>
        ⟨fun c h =>
          ⟨fun s => h.desc ⟨s.x, fun j => s.ι.app j, fun j j' f => s.ι.naturality f⟩, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j, by
            cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s m w <;> rcases s with ⟨_, _, _⟩ <;> exact h.uniq _ m w⟩⟩ }

section

variable {E : Type u₃} [ℰ : Category.{v₃} E]

variable (F : C ⥤ D) (G : D ⥤ E)

instance compReflectsLimit [ReflectsLimit K F] [ReflectsLimit (K ⋙ F) G] : ReflectsLimit K (F ⋙ G) :=
  ⟨fun c h => ReflectsLimit.reflects (ReflectsLimit.reflects h)⟩

instance compReflectsLimitsOfShape [ReflectsLimitsOfShape J F] [ReflectsLimitsOfShape J G] :
    ReflectsLimitsOfShape J (F ⋙ G) :=
  {  }

instance compReflectsLimits [ReflectsLimitsOfSize.{w', w} F] [ReflectsLimitsOfSize.{w', w} G] :
    ReflectsLimitsOfSize.{w', w} (F ⋙ G) :=
  {  }

instance compReflectsColimit [ReflectsColimit K F] [ReflectsColimit (K ⋙ F) G] : ReflectsColimit K (F ⋙ G) :=
  ⟨fun c h => ReflectsColimit.reflects (ReflectsColimit.reflects h)⟩

instance compReflectsColimitsOfShape [ReflectsColimitsOfShape J F] [ReflectsColimitsOfShape J G] :
    ReflectsColimitsOfShape J (F ⋙ G) :=
  {  }

instance compReflectsColimits [ReflectsColimitsOfSize.{w', w} F] [ReflectsColimitsOfSize.{w', w} G] :
    ReflectsColimitsOfSize.{w', w} (F ⋙ G) :=
  {  }

/-- If `F ⋙ G` preserves limits for `K`, and `G` reflects limits for `K ⋙ F`,
then `F` preserves limits for `K`. -/
def preservesLimitOfReflectsOfPreserves [PreservesLimit K (F ⋙ G)] [ReflectsLimit (K ⋙ F) G] : PreservesLimit K F :=
  ⟨fun c h => by
    apply is_limit_of_reflects G
    apply is_limit_of_preserves (F ⋙ G) h⟩

/-- If `F ⋙ G` preserves limits of shape `J` and `G` reflects limits of shape `J`, then `F` preserves
limits of shape `J`.
-/
def preservesLimitsOfShapeOfReflectsOfPreserves [PreservesLimitsOfShape J (F ⋙ G)] [ReflectsLimitsOfShape J G] :
    PreservesLimitsOfShape J F where
  PreservesLimit := fun K => preservesLimitOfReflectsOfPreserves F G

/-- If `F ⋙ G` preserves limits and `G` reflects limits, then `F` preserves limits. -/
def preservesLimitsOfReflectsOfPreserves [PreservesLimitsOfSize.{w', w} (F ⋙ G)] [ReflectsLimitsOfSize.{w', w} G] :
    PreservesLimitsOfSize.{w', w} F where
  PreservesLimitsOfShape := fun J 𝒥₁ => preserves_limits_of_shape_of_reflects_of_preserves F G

/-- Transfer reflection of limits along a natural isomorphism in the diagram. -/
def reflectsLimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsLimit K₁ F] : ReflectsLimit K₂ F where
  reflects := fun c t => by
    apply is_limit.postcompose_inv_equiv h c (is_limit_of_reflects F _)
    apply ((is_limit.postcompose_inv_equiv (iso_whisker_right h F : _) _).symm t).ofIsoLimit _
    exact
      cones.ext (iso.refl _)
        (by
          tidy)

/-- Transfer reflection of a limit along a natural isomorphism in the functor. -/
def reflectsLimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimit K F] : ReflectsLimit K G where
  reflects := fun c t => ReflectsLimit.reflects (IsLimit.mapConeEquiv h.symm t)

/-- Transfer reflection of limits of shape along a natural isomorphism in the functor. -/
def reflectsLimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfShape J F] :
    ReflectsLimitsOfShape J G where
  ReflectsLimit := fun K => reflectsLimitOfNatIso K h

/-- Transfer reflection of limits along a natural isomorphism in the functor. -/
def reflectsLimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsLimitsOfSize.{w', w} F] :
    ReflectsLimitsOfSize.{w', w} G where
  ReflectsLimitsOfShape := fun J 𝒥₁ => reflects_limits_of_shape_of_nat_iso h

/-- If the limit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the limit of `F`.
-/
def reflectsLimitOfReflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [ReflectsIsomorphisms G] [HasLimit F]
    [PreservesLimit F G] : ReflectsLimit F G where
  reflects := fun c t => by
    apply is_limit.of_point_iso (limit.is_limit F)
    change is_iso ((cones.forget _).map ((limit.is_limit F).liftConeMorphism c))
    apply (cones.forget F).map_is_iso _
    apply is_iso_of_reflects_iso _ (cones.functoriality F G)
    refine' t.hom_is_iso (is_limit_of_preserves G (limit.is_limit F)) _

/-- If `C` has limits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects limits of shape `J`.
-/
def reflectsLimitsOfShapeOfReflectsIsomorphisms {G : C ⥤ D} [ReflectsIsomorphisms G] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J G] : ReflectsLimitsOfShape J G where
  ReflectsLimit := fun F => reflectsLimitOfReflectsIsomorphisms F G

/-- If `C` has limits and `G` preserves limits, then if `G` reflects isomorphisms then it reflects
limits.
-/
def reflectsLimitsOfReflectsIsomorphisms {G : C ⥤ D} [ReflectsIsomorphisms G] [HasLimitsOfSize.{w', w} C]
    [PreservesLimitsOfSize.{w', w} G] : ReflectsLimitsOfSize.{w', w} G where
  ReflectsLimitsOfShape := fun J 𝒥₁ => reflects_limits_of_shape_of_reflects_isomorphisms

/-- If `F ⋙ G` preserves colimits for `K`, and `G` reflects colimits for `K ⋙ F`,
then `F` preserves colimits for `K`. -/
def preservesColimitOfReflectsOfPreserves [PreservesColimit K (F ⋙ G)] [ReflectsColimit (K ⋙ F) G] :
    PreservesColimit K F :=
  ⟨fun c h => by
    apply is_colimit_of_reflects G
    apply is_colimit_of_preserves (F ⋙ G) h⟩

/-- If `F ⋙ G` preserves colimits of shape `J` and `G` reflects colimits of shape `J`, then `F`
preserves colimits of shape `J`.
-/
def preservesColimitsOfShapeOfReflectsOfPreserves [PreservesColimitsOfShape J (F ⋙ G)] [ReflectsColimitsOfShape J G] :
    PreservesColimitsOfShape J F where
  PreservesColimit := fun K => preservesColimitOfReflectsOfPreserves F G

/-- If `F ⋙ G` preserves colimits and `G` reflects colimits, then `F` preserves colimits. -/
def preservesColimitsOfReflectsOfPreserves [PreservesColimitsOfSize.{w', w} (F ⋙ G)]
    [ReflectsColimitsOfSize.{w', w} G] : PreservesColimitsOfSize.{w', w} F where
  PreservesColimitsOfShape := fun J 𝒥₁ => preserves_colimits_of_shape_of_reflects_of_preserves F G

/-- Transfer reflection of colimits along a natural isomorphism in the diagram. -/
def reflectsColimitOfIsoDiagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [ReflectsColimit K₁ F] :
    ReflectsColimit K₂ F where
  reflects := fun c t => by
    apply is_colimit.precompose_hom_equiv h c (is_colimit_of_reflects F _)
    apply ((is_colimit.precompose_hom_equiv (iso_whisker_right h F : _) _).symm t).ofIsoColimit _
    exact
      cocones.ext (iso.refl _)
        (by
          tidy)

/-- Transfer reflection of a colimit along a natural isomorphism in the functor. -/
def reflectsColimitOfNatIso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimit K F] : ReflectsColimit K G where
  reflects := fun c t => ReflectsColimit.reflects (IsColimit.mapCoconeEquiv h.symm t)

/-- Transfer reflection of colimits of shape along a natural isomorphism in the functor. -/
def reflectsColimitsOfShapeOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfShape J F] :
    ReflectsColimitsOfShape J G where
  ReflectsColimit := fun K => reflectsColimitOfNatIso K h

/-- Transfer reflection of colimits along a natural isomorphism in the functor. -/
def reflectsColimitsOfNatIso {F G : C ⥤ D} (h : F ≅ G) [ReflectsColimitsOfSize.{w, w'} F] :
    ReflectsColimitsOfSize.{w, w'} G where
  ReflectsColimitsOfShape := fun J 𝒥₁ => reflects_colimits_of_shape_of_nat_iso h

/-- If the colimit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the colimit of `F`.
-/
def reflectsColimitOfReflectsIsomorphisms (F : J ⥤ C) (G : C ⥤ D) [ReflectsIsomorphisms G] [HasColimit F]
    [PreservesColimit F G] : ReflectsColimit F G where
  reflects := fun c t => by
    apply is_colimit.of_point_iso (colimit.is_colimit F)
    change is_iso ((cocones.forget _).map ((colimit.is_colimit F).descCoconeMorphism c))
    apply (cocones.forget F).map_is_iso _
    apply is_iso_of_reflects_iso _ (cocones.functoriality F G)
    refine' (is_colimit_of_preserves G (colimit.is_colimit F)).hom_is_iso t _

/-- If `C` has colimits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects colimits of shape `J`.
-/
def reflectsColimitsOfShapeOfReflectsIsomorphisms {G : C ⥤ D} [ReflectsIsomorphisms G] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J G] : ReflectsColimitsOfShape J G where
  ReflectsColimit := fun F => reflectsColimitOfReflectsIsomorphisms F G

/-- If `C` has colimits and `G` preserves colimits, then if `G` reflects isomorphisms then it reflects
colimits.
-/
def reflectsColimitsOfReflectsIsomorphisms {G : C ⥤ D} [ReflectsIsomorphisms G] [HasColimitsOfSize.{w', w} C]
    [PreservesColimitsOfSize.{w', w} G] : ReflectsColimitsOfSize.{w', w} G where
  ReflectsColimitsOfShape := fun J 𝒥₁ => reflects_colimits_of_shape_of_reflects_isomorphisms

end

variable (F : C ⥤ D)

/-- A fully faithful functor reflects limits. -/
def fullyFaithfulReflectsLimits [Full F] [Faithful F] : ReflectsLimitsOfSize.{w, w'} F where
  ReflectsLimitsOfShape := fun J 𝒥₁ =>
    { ReflectsLimit := fun K =>
        { reflects := fun c t =>
            (is_limit.mk_cone_morphism fun s => (cones.functoriality K F).preimage (t.liftConeMorphism _)) <| by
              apply fun s m => (cones.functoriality K F).map_injective _
              rw [functor.image_preimage]
              apply t.uniq_cone_morphism } }

/-- A fully faithful functor reflects colimits. -/
def fullyFaithfulReflectsColimits [Full F] [Faithful F] : ReflectsColimitsOfSize.{w, w'} F where
  ReflectsColimitsOfShape := fun J 𝒥₁ =>
    { ReflectsColimit := fun K =>
        { reflects := fun c t =>
            (is_colimit.mk_cocone_morphism fun s => (cocones.functoriality K F).preimage (t.descCoconeMorphism _)) <| by
              apply fun s m => (cocones.functoriality K F).map_injective _
              rw [functor.image_preimage]
              apply t.uniq_cocone_morphism } }

end CategoryTheory.Limits

