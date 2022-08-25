/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.CategoryTheory.Sites.Limits
import Mathbin.CategoryTheory.Functor.Flat
import Mathbin.CategoryTheory.Limits.Preserves.Filtered
import Mathbin.CategoryTheory.Sites.LeftExact

/-!
# Cover-preserving functors between sites.

We define cover-preserving functors between sites as functors that push covering sieves to
covering sieves. A cover-preserving and compatible-preserving functor `G : C ⥤ D` then pulls
sheaves on `D` back to sheaves on `C` via `G.op ⋙ -`.

## Main definitions

* `category_theory.cover_preserving`: a functor between sites is cover-preserving if it
pushes covering sieves to covering sieves
* `category_theory.compatible_preserving`: a functor between sites is compatible-preserving
if it pushes compatible families of elements to compatible families.
* `category_theory.pullback_sheaf`: the pullback of a sheaf along a cover-preserving and
compatible-preserving functor.
* `category_theory.sites.pullback`: the induced functor `Sheaf K A ⥤ Sheaf J A` for a
cover-preserving and compatible-preserving functor `G : (C, J) ⥤ (D, K)`.
* `category_theory.sites.pushforward`: the induced functor `Sheaf J A ⥤ Sheaf K A` for a
cover-preserving and compatible-preserving functor `G : (C, J) ⥤ (D, K)`.
* `category_theory.sites.pushforward`: the induced functor `Sheaf J A ⥤ Sheaf K A` for a
cover-preserving and compatible-preserving functor `G : (C, J) ⥤ (D, K)`.

## Main results

- `category_theory.sites.whiskering_left_is_sheaf_of_cover_preserving`: If `G : C ⥤ D` is
cover-preserving and compatible-preserving, then `G ⋙ -` (`uᵖ`) as a functor
`(Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)` of presheaves maps sheaves to sheaves.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.3.
* https://stacks.math.columbia.edu/tag/00WW

-/


universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

open CategoryTheory

open Opposite

open CategoryTheory.Presieve.FamilyOfElements

open CategoryTheory.Presieve

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {A : Type u₃} [Category.{v₃} A]

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

variable {L : GrothendieckTopology A}

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is *cover-preserving*
if for all covering sieves `R` in `C`, `R.pushforward_functor G` is a covering sieve in `D`.
-/
@[nolint has_nonempty_instance]
structure CoverPreserving (G : C ⥤ D) : Prop where
  cover_preserve : ∀ {U : C} {S : Sieve U} (hS : S ∈ J U), S.FunctorPushforward G ∈ K (G.obj U)

/-- The identity functor on a site is cover-preserving. -/
theorem id_cover_preserving : CoverPreserving J J (𝟭 _) :=
  ⟨fun U S hS => by
    simpa using hS⟩

variable (J) (K)

/-- The composition of two cover-preserving functors is cover-preserving. -/
theorem CoverPreserving.comp {F} (hF : CoverPreserving J K F) {G} (hG : CoverPreserving K L G) :
    CoverPreserving J L (F ⋙ G) :=
  ⟨fun U S hS => by
    rw [sieve.functor_pushforward_comp]
    exact hG.cover_preserve (hF.cover_preserve hS)⟩

/-- A functor `G : (C, J) ⥤ (D, K)` between sites is called compatible preserving if for each
compatible family of elements at `C` and valued in `G.op ⋙ ℱ`, and each commuting diagram
`f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂`, `x g₁` and `x g₂` coincide when restricted via `fᵢ`.
This is actually stronger than merely preserving compatible families because of the definition of
`functor_pushforward` used.
-/
@[nolint has_nonempty_instance]
structure CompatiblePreserving (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  Compatible :
    ∀ (ℱ : SheafOfTypes.{w} K) {Z} {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.val) T} (h : x.Compatible) {Y₁ Y₂}
      {X} (f₁ : X ⟶ G.obj Y₁) (f₂ : X ⟶ G.obj Y₂) {g₁ : Y₁ ⟶ Z} {g₂ : Y₂ ⟶ Z} (hg₁ : T g₁) (hg₂ : T g₂)
      (eq : f₁ ≫ G.map g₁ = f₂ ≫ G.map g₂), ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)

variable {J K} {G : C ⥤ D} (hG : CompatiblePreserving.{w} K G) (ℱ : SheafOfTypes.{w} K) {Z : C}

variable {T : Presieve Z} {x : FamilyOfElements (G.op ⋙ ℱ.val) T} (h : x.Compatible)

include h hG

/-- `compatible_preserving` functors indeed preserve compatible families. -/
theorem Presieve.FamilyOfElements.Compatible.functor_pushforward : (x.FunctorPushforward G).Compatible := by
  rintro Z₁ Z₂ W g₁ g₂ f₁' f₂' H₁ H₂ eq
  unfold family_of_elements.functor_pushforward
  rcases get_functor_pushforward_structure H₁ with ⟨X₁, f₁, h₁, hf₁, rfl⟩
  rcases get_functor_pushforward_structure H₂ with ⟨X₂, f₂, h₂, hf₂, rfl⟩
  suffices : ℱ.val.map (g₁ ≫ h₁).op (x f₁ hf₁) = ℱ.val.map (g₂ ≫ h₂).op (x f₂ hf₂)
  simpa using this
  apply hG.compatible ℱ h _ _ hf₁ hf₂
  simpa using Eq

@[simp]
theorem CompatiblePreserving.apply_map {Y : C} {f : Y ⟶ Z} (hf : T f) :
    x.FunctorPushforward G (G.map f) (image_mem_functor_pushforward G T hf) = x f hf := by
  unfold family_of_elements.functor_pushforward
  rcases e₁ : get_functor_pushforward_structure (image_mem_functor_pushforward G T hf) with ⟨X, g, f', hg, eq⟩
  simpa using
    hG.compatible ℱ h f' (𝟙 _) hg hf
      (by
        simp [Eq])

omit h hG

open Limits.WalkingCospan

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.constructor "constructor") [])
          (group (Tactic.intro "intro" [`ℱ `Z `T `x `hx `Y₁ `Y₂ `X `f₁ `f₂ `g₁ `g₂ `hg₁ `hg₂ `e]) [])
          (group
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `c
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `cone
                 [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                   (Term.app `cospan [`g₁ `g₂])
                   " ⋙ "
                   `G)]))]
              ":="
              (Term.app
               (Term.proj
                (Term.app
                 `cones.postcompose
                 [(Term.proj
                   (Term.app
                    `diagram_iso_cospan
                    [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                      (Term.app `cospan [`g₁ `g₂])
                      " ⋙ "
                      `G)])
                   "."
                   `inv)])
                "."
                `obj)
               [(Term.app `pullback_cone.mk [`f₁ `f₂ `e])]))))
           [])
          (group
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letIdDecl
              `c'
              []
              []
              ":="
              (Term.app
               `is_cofiltered.cone
               [(CategoryTheory.Functor.CategoryTheory.Functor.Basic.«term_⋙_»
                 (Term.app `structured_arrow_cone.to_diagram [`c])
                 " ⋙ "
                 (Term.app `structured_arrow.pre [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))]))))
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`eq₁ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 `f₁
                 "="
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   `c'.X.hom
                   " ≫ "
                   (Term.app `G.map [(Term.proj (Term.app `c'.π.app [`left]) "." `right)]))
                  " ≫ "
                  (Term.app
                   `eq_to_hom
                   [(Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] [] []) [])])))]))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.tacticErw__
                    "erw"
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.proj (Term.app `c'.π.app [`left]) "." `w))] "]")
                    [])
                   [])
                  (group (Tactic.dsimp' "dsimp'" [] [] [] [] []) [])
                  (group (Tactic.simp "simp" [] [] [] [] []) [])]))))))
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`eq₂ []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 `f₂
                 "="
                 (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                  (CategoryTheory.CategoryTheory.Category.Basic.«term_≫_»
                   `c'.X.hom
                   " ≫ "
                   (Term.app `G.map [(Term.proj (Term.app `c'.π.app [`right]) "." `right)]))
                  " ≫ "
                  (Term.app
                   `eq_to_hom
                   [(Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] [] []) [])])))]))))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.tacticErw__
                    "erw"
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.proj (Term.app `c'.π.app [`right]) "." `w))] "]")
                    [])
                   [])
                  (group (Tactic.dsimp' "dsimp'" [] [] [] [] []) [])
                  (group (Tactic.simp "simp" [] [] [] [] []) [])]))))))
           [])
          (group
           (Mathlib.Tactic.Conv.convLHS
            "conv_lhs"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq₁)] "]")) [])])))
           [])
          (group
           (Mathlib.Tactic.Conv.convRHS
            "conv_rhs"
            []
            []
            "=>"
            (Tactic.Conv.convSeq
             (Tactic.Conv.convSeq1Indented
              [(group (Tactic.Conv.convRw__ "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `eq₂)] "]")) [])])))
           [])
          (group
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `op_comp)
              ","
              (Tactic.simpLemma [] [] `functor.map_comp)
              ","
              (Tactic.simpLemma [] [] `types_comp_apply)
              ","
              (Tactic.simpLemma [] [] `eq_to_hom_op)
              ","
              (Tactic.simpLemma [] [] `eq_to_hom_map)]
             "]"]
            [])
           [])
          (group (Tactic.congr' "congr" [(num "1")] []) [])
          (group
           (Tactic.injection "injection" (Term.app `c'.π.naturality [`walking_cospan.hom.inl]) ["with" ["_" `e₁]])
           [])
          (group
           (Tactic.injection "injection" (Term.app `c'.π.naturality [`walking_cospan.hom.inr]) ["with" ["_" `e₂]])
           [])
          (group
           (Tactic.exact
            "exact"
            (Term.app
             `hx
             [(Term.proj (Term.app `c'.π.app [`left]) "." `right)
              (Term.proj (Term.app `c'.π.app [`right]) "." `right)
              `hg₁
              `hg₂
              (Term.app `e₁.symm.trans [`e₂])]))
           [])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `hx
        [(Term.proj (Term.app `c'.π.app [`left]) "." `right)
         (Term.proj (Term.app `c'.π.app [`right]) "." `right)
         `hg₁
         `hg₂
         (Term.app `e₁.symm.trans [`e₂])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hx
       [(Term.proj (Term.app `c'.π.app [`left]) "." `right)
        (Term.proj (Term.app `c'.π.app [`right]) "." `right)
        `hg₁
        `hg₂
        (Term.app `e₁.symm.trans [`e₂])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `e₁.symm.trans [`e₂])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `e₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `e₁.symm.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `e₁.symm.trans [`e₂]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hg₂
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hg₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `c'.π.app [`right]) "." `right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `c'.π.app [`right])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `right
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c'.π.app
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `c'.π.app [`right]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `c'.π.app [`left]) "." `right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `c'.π.app [`left])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `left
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `c'.π.app
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `c'.π.app [`left]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.injection
       "injection"
       (Term.app `c'.π.naturality [`walking_cospan.hom.inr])
       ["with" ["_" `e₂]])-/-- failed to format: format: uncaught backtrack exception
theorem
  compatible_preserving_of_flat
  { C : Type u₁ }
      [ Category .{ v₁ } C ]
      { D : Type u₁ }
      [ Category .{ v₁ } D ]
      ( K : GrothendieckTopology D )
      ( G : C ⥤ D )
      [ RepresentablyFlat G ]
    : CompatiblePreserving K G
  :=
    by
      constructor
        intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ e
        let
          c
            : cone cospan g₁ g₂ ⋙ G
            :=
            cones.postcompose diagram_iso_cospan cospan g₁ g₂ ⋙ G . inv . obj pullback_cone.mk f₁ f₂ e
        let c' := is_cofiltered.cone structured_arrow_cone.to_diagram c ⋙ structured_arrow.pre _ _ _
        have
          eq₁
            : f₁ = c'.X.hom ≫ G.map c'.π.app left . right ≫ eq_to_hom by simp
            :=
            by erw [ ← c'.π.app left . w ] dsimp' simp
        have
          eq₂
            : f₂ = c'.X.hom ≫ G.map c'.π.app right . right ≫ eq_to_hom by simp
            :=
            by erw [ ← c'.π.app right . w ] dsimp' simp
        conv_lhs => rw [ eq₁ ]
        conv_rhs => rw [ eq₂ ]
        simp only [ op_comp , functor.map_comp , types_comp_apply , eq_to_hom_op , eq_to_hom_map ]
        congr 1
        injection c'.π.naturality walking_cospan.hom.inl with _ e₁
        injection c'.π.naturality walking_cospan.hom.inr with _ e₂
        exact hx c'.π.app left . right c'.π.app right . right hg₁ hg₂ e₁.symm.trans e₂

/-- If `G` is cover-preserving and compatible-preserving,
then `G.op ⋙ _` pulls sheaves back to sheaves.

This result is basically <https://stacks.math.columbia.edu/tag/00WW>.
-/
theorem pullback_is_sheaf_of_cover_preserving {G : C ⥤ D} (hG₁ : CompatiblePreserving.{v₃} K G)
    (hG₂ : CoverPreserving J K G) (ℱ : Sheaf K A) : Presheaf.IsSheaf J (G.op ⋙ ℱ.val) := by
  intro X U S hS x hx
  change family_of_elements (G.op ⋙ ℱ.val ⋙ coyoneda.obj (op X)) _ at x
  let H := ℱ.2 X _ (hG₂.cover_preserve hS)
  let hx' := hx.functor_pushforward hG₁ (sheaf_over ℱ X)
  constructor
  swap
  · apply H.amalgamate (x.functor_pushforward G)
    exact hx'
    
  constructor
  · intro V f hf
    convert H.is_amalgamation hx' (G.map f) (image_mem_functor_pushforward G S hf)
    rw [hG₁.apply_map (sheaf_over ℱ X) hx]
    
  · intro y hy
    refine' H.is_separated_for _ y _ _ (H.is_amalgamation (hx.functor_pushforward hG₁ (sheaf_over ℱ X)))
    rintro V f ⟨Z, f', g', h, rfl⟩
    erw [family_of_elements.comp_of_compatible (S.functor_pushforward G) hx' (image_mem_functor_pushforward G S h) g']
    dsimp'
    simp [hG₁.apply_map (sheaf_over ℱ X) hx h, ← hy f' h]
    

/-- The pullback of a sheaf along a cover-preserving and compatible-preserving functor. -/
def pullbackSheaf {G : C ⥤ D} (hG₁ : CompatiblePreserving K G) (hG₂ : CoverPreserving J K G) (ℱ : Sheaf K A) :
    Sheaf J A :=
  ⟨G.op ⋙ ℱ.val, pullback_is_sheaf_of_cover_preserving hG₁ hG₂ ℱ⟩

variable (A)

/-- The induced functor from `Sheaf K A ⥤ Sheaf J A` given by `G.op ⋙ _`
if `G` is cover-preserving and compatible-preserving.
-/
@[simps]
def Sites.pullback {G : C ⥤ D} (hG₁ : CompatiblePreserving K G) (hG₂ : CoverPreserving J K G) :
    Sheaf K A ⥤ Sheaf J A where
  obj := fun ℱ => pullbackSheaf hG₁ hG₂ ℱ
  map := fun _ _ f => ⟨((whiskeringLeft _ _ _).obj G.op).map f.val⟩
  map_id' := fun ℱ => by
    ext1
    apply ((whiskering_left _ _ _).obj G.op).map_id
  map_comp' := fun _ _ _ f g => by
    ext1
    apply ((whiskering_left _ _ _).obj G.op).map_comp

end CategoryTheory

namespace CategoryTheory

variable {C : Type v₁} [SmallCategory C] {D : Type v₁} [SmallCategory D]

variable (A : Type u₂) [Category.{v₁} A]

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

instance [HasLimits A] : CreatesLimits (sheafToPresheaf J A) :=
  CategoryTheory.Sheaf.CategoryTheory.SheafToPresheaf.CategoryTheory.createsLimits.{u₂, v₁, v₁}

-- The assumptions so that we have sheafification
variable [ConcreteCategory.{v₁} A] [PreservesLimits (forget A)] [HasColimits A] [HasLimits A]

variable [PreservesFilteredColimits (forget A)] [ReflectsIsomorphisms (forget A)]

attribute [local instance] reflects_limits_of_reflects_isomorphisms

instance {X : C} : IsCofiltered (J.cover X) :=
  inferInstance

/-- The pushforward functor `Sheaf J A ⥤ Sheaf K A` associated to a functor `G : C ⥤ D` in the
same direction as `G`. -/
@[simps]
def Sites.pushforward (G : C ⥤ D) : Sheaf J A ⥤ Sheaf K A :=
  sheafToPresheaf J A ⋙ lan G.op ⋙ presheafToSheaf K A

instance (G : C ⥤ D) [RepresentablyFlat G] : PreservesFiniteLimits (Sites.pushforward A J K G) := by
  apply comp_preserves_finite_limits with { instances := false }
  · infer_instance
    
  apply comp_preserves_finite_limits with { instances := false }
  · apply CategoryTheory.lanPreservesFiniteLimitsOfFlat
    
  · apply CategoryTheory.presheafToSheaf.Limits.preservesFiniteLimits.{u₂, v₁, v₁}
    infer_instance
    

/-- The pushforward functor is left adjoint to the pullback functor. -/
def Sites.pullbackPushforwardAdjunction {G : C ⥤ D} (hG₁ : CompatiblePreserving K G) (hG₂ : CoverPreserving J K G) :
    Sites.pushforward A J K G ⊣ Sites.pullback A hG₁ hG₂ :=
  ((lan.adjunction A G.op).comp (sheafificationAdjunction K A)).restrictFullyFaithful (sheafToPresheaf J A) (𝟭 _)
    (NatIso.ofComponents (fun _ => Iso.refl _) fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm)
    (NatIso.ofComponents (fun _ => Iso.refl _) fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm)

end CategoryTheory

