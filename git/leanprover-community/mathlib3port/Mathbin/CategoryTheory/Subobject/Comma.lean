/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Subobject.WellPowered

/-!
# Subobjects in the category of structured arrows

We compute the subobjects of an object `A` in the category `structured_arrow S T` for `T : C ⥤ D`
and `S : D` as a subtype of the subobjects of `A.right`. We deduce that `structured_arrow S T` is
well-powered if `C` is.

## Main declarations
* `structured_arrow.equiv_subtype`: the order-equivalence between `subobject A` and a subtype of
  `subobject A.right`.

## Implementation notes
Our computation requires that `C` has all limits and `T` preserves all limits. Furthermore, we
require that the morphisms of `C` and `D` are in the same universe. It is possible that both of
these requirements can be relaxed by refining the results about limits in comma categories.

We also provide the dual results. As usual, we use `subobject (op A)` for the quotient objects of
`A`.

-/


noncomputable section

open CategoryTheory.Limits Opposite

universe v u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

namespace StructuredArrow

variable {S : D} {T : C ⥤ D}

/-- Every subobject of a structured arrow can be projected to a subobject of the underlying
    object. -/
def projectSubobject [HasLimits C] [PreservesLimits T] {A : StructuredArrow S T} : Subobject A → Subobject A.right := by
  refine' subobject.lift (fun P f hf => subobject.mk f.right) _
  intro P Q f g hf hg i hi
  refine' subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i) _
  exact congr_arg comma_morphism.right hi

@[simp]
theorem project_subobject_mk [HasLimits C] [PreservesLimits T] {A P : StructuredArrow S T} (f : P ⟶ A) [Mono f] :
    projectSubobject (Subobject.mk f) = Subobject.mk f.right :=
  rfl

theorem project_subobject_factors [HasLimits C] [PreservesLimits T] {A : StructuredArrow S T} :
    ∀ P : Subobject A, ∃ q, q ≫ T.map (projectSubobject P).arrow = A.Hom :=
  (Subobject.ind _) fun P f hf =>
    ⟨P.Hom ≫ T.map (Subobject.underlyingIso _).inv, by
      dsimp'
      simp [T.map_comp]⟩

/-- A subobject of the underlying object of a structured arrow can be lifted to a subobject of
    the structured arrow, provided that there is a morphism making the subobject into a structured
    arrow. -/
@[simp]
def liftSubobject {A : StructuredArrow S T} (P : Subobject A.right) {q} (hq : q ≫ T.map P.arrow = A.Hom) :
    Subobject A :=
  Subobject.mk (homMk P.arrow hq : mk q ⟶ A)

/-- Projecting and then lifting a subobject recovers the original subobject, because there is at
    most one morphism making the projected subobject into a structured arrow. -/
theorem lift_project_subobject [HasLimits C] [PreservesLimits T] {A : StructuredArrow S T} :
    ∀ (P : Subobject A) {q} (hq : q ≫ T.map (projectSubobject P).arrow = A.Hom),
      liftSubobject (projectSubobject P) hq = P :=
  Subobject.ind _
    (by
      intro P f hf q hq
      fapply subobject.mk_eq_mk_of_comm
      · fapply iso_mk
        · exact subobject.underlying_iso _
          
        · exact
            (cancel_mono (T.map f.right)).1
              (by
                dsimp'
                simpa [T.map_comp] using hq)
          
        
      · exact
          ext _ _
            (by
              dsimp'
              simp )
        )

/-- If `A : S → T.obj B` is a structured arrow for `S : D` and `T : C ⥤ D`, then we can explicitly
    describe the subobjects of `A` as the subobjects `P` of `B` in `C` for which `A.hom` factors
    through the image of `P` under `T`. -/
@[simps]
def subobjectEquiv [HasLimits C] [PreservesLimits T] (A : StructuredArrow S T) :
    Subobject A ≃o { P : Subobject A.right // ∃ q, q ≫ T.map P.arrow = A.Hom } where
  toFun := fun P => ⟨projectSubobject P, project_subobject_factors P⟩
  invFun := fun P => liftSubobject P.val P.Prop.some_spec
  left_inv := fun P => lift_project_subobject _ _
  right_inv := fun P =>
    Subtype.ext
      (by
        simp )
  map_rel_iff' :=
    Subobject.ind₂ _
      (by
        intro P Q f g hf hg
        refine' ⟨fun h => subobject.mk_le_mk_of_comm _ (ext _ _ _), fun h => _⟩
        · refine' hom_mk (subobject.of_mk_le_mk _ _ h) ((cancel_mono (T.map g.right)).1 _)
          simp [T.map_comp]
          
        · simp only [← mono_over.mk'_arrow, ← subobject.of_mk_le_mk_comp, ← comma.comp_right, ← hom_mk_right]
          
        · refine' subobject.mk_le_mk_of_comm (subobject.of_mk_le_mk _ _ h).right _
          exact congr_arg comma_morphism.right (subobject.of_mk_le_mk_comp h)
          )

/-- If `C` is well-powered and complete and `T` preserves limits, then `structured_arrow S T` is
    well-powered. -/
instance well_powered_structured_arrow [WellPowered C] [HasLimits C] [PreservesLimits T] :
    WellPowered (StructuredArrow S T) where subobject_small := fun X => small_map (subobjectEquiv X).toEquiv

end StructuredArrow

namespace CostructuredArrow

variable {S : C ⥤ D} {T : D}

/-- Every quotient of a costructured arrow can be projected to a quotient of the underlying
    object. -/
def projectQuotient [HasColimits C] [PreservesColimits S] {A : CostructuredArrow S T} :
    Subobject (op A) → Subobject (op A.left) := by
  refine' subobject.lift (fun P f hf => subobject.mk f.unop.left.op) _
  intro P Q f g hf hg i hi
  refine' subobject.mk_eq_mk_of_comm _ _ ((proj S T).mapIso i.unop).op (Quiver.Hom.unop_inj _)
  have := congr_arg Quiver.Hom.unop hi
  simpa using congr_arg comma_morphism.left this

@[simp]
theorem project_quotient_mk [HasColimits C] [PreservesColimits S] {A : CostructuredArrow S T}
    {P : (CostructuredArrow S T)ᵒᵖ} (f : P ⟶ op A) [Mono f] :
    projectQuotient (Subobject.mk f) = Subobject.mk f.unop.left.op :=
  rfl

theorem project_quotient_factors [HasColimits C] [PreservesColimits S] {A : CostructuredArrow S T} :
    ∀ P : Subobject (op A), ∃ q, S.map (projectQuotient P).arrow.unop ≫ q = A.Hom :=
  (Subobject.ind _) fun P f hf =>
    ⟨S.map (Subobject.underlyingIso _).unop.inv ≫ P.unop.Hom, by
      dsimp'
      rw [← category.assoc, ← S.map_comp, ← unop_comp]
      simp ⟩

/-- A quotient of the underlying object of a costructured arrow can be lifted to a quotient of
    the costructured arrow, provided that there is a morphism making the quotient into a
    costructured arrow. -/
@[simp]
def liftQuotient {A : CostructuredArrow S T} (P : Subobject (op A.left)) {q} (hq : S.map P.arrow.unop ≫ q = A.Hom) :
    Subobject (op A) :=
  Subobject.mk (homMk P.arrow.unop hq : A ⟶ mk q).op

/-- Technical lemma for `lift_project_quotient`. -/
@[simp]
theorem unop_left_comp_underlying_iso_hom_unop {A : CostructuredArrow S T} {P : (CostructuredArrow S T)ᵒᵖ}
    (f : P ⟶ op A) [Mono f.unop.left.op] :
    f.unop.left ≫ (Subobject.underlyingIso f.unop.left.op).Hom.unop = (Subobject.mk f.unop.left.op).arrow.unop := by
  conv_lhs => congr rw [← Quiver.Hom.unop_op f.unop.left]
  rw [← unop_comp, subobject.underlying_iso_hom_comp_eq_mk]

/-- Projecting and then lifting a quotient recovers the original quotient, because there is at most
    one morphism making the projected quotient into a costructured arrow. -/
theorem lift_project_quotient [HasColimits C] [PreservesColimits S] {A : CostructuredArrow S T} :
    ∀ (P : Subobject (op A)) {q} (hq : S.map (projectQuotient P).arrow.unop ≫ q = A.Hom),
      liftQuotient (projectQuotient P) hq = P :=
  Subobject.ind _
    (by
      intro P f hf q hq
      fapply subobject.mk_eq_mk_of_comm
      · refine' (iso.op (iso_mk _ _) : _ ≅ op (unop P))
        · exact (subobject.underlying_iso f.unop.left.op).unop
          
        · refine' (cancel_epi (S.map f.unop.left)).1 _
          simpa [category.assoc, S.map_comp] using hq
          
        
      · exact
          Quiver.Hom.unop_inj
            (ext _ _
              (by
                dsimp'
                simp ))
        )

/-- Technical lemma for `quotient_equiv`. -/
theorem unop_left_comp_of_mk_le_mk_unop {A : CostructuredArrow S T} {P Q : (CostructuredArrow S T)ᵒᵖ} {f : P ⟶ op A}
    {g : Q ⟶ op A} [Mono f.unop.left.op] [Mono g.unop.left.op]
    (h : Subobject.mk f.unop.left.op ≤ Subobject.mk g.unop.left.op) :
    g.unop.left ≫ (Subobject.ofMkLeMk f.unop.left.op g.unop.left.op h).unop = f.unop.left := by
  conv_lhs => congr rw [← Quiver.Hom.unop_op g.unop.left]
  rw [← unop_comp]
  simp only [← subobject.of_mk_le_mk_comp, ← Quiver.Hom.unop_op]

/-- If `A : S.obj B ⟶ T` is a costructured arrow for `S : C ⥤ D` and `T : D`, then we can
    explicitly describe the quotients of `A` as the quotients `P` of `B` in `C` for which `A.hom`
    factors through the image of `P` under `S`. -/
def quotientEquiv [HasColimits C] [PreservesColimits S] (A : CostructuredArrow S T) :
    Subobject (op A) ≃o { P : Subobject (op A.left) // ∃ q, S.map P.arrow.unop ≫ q = A.Hom } where
  toFun := fun P => ⟨projectQuotient P, project_quotient_factors P⟩
  invFun := fun P => liftQuotient P.val P.Prop.some_spec
  left_inv := fun P => lift_project_quotient _ _
  right_inv := fun P =>
    Subtype.ext
      (by
        simp )
  map_rel_iff' :=
    Subobject.ind₂ _
      (by
        intro P Q f g hf hg
        refine' ⟨fun h => subobject.mk_le_mk_of_comm _ (Quiver.Hom.unop_inj (ext _ _ _)), fun h => _⟩
        · refine' (hom_mk (subobject.of_mk_le_mk _ _ h).unop ((cancel_epi (S.map g.unop.left)).1 _)).op
          dsimp' only [← mono_over.mk'_arrow]
          rw [← category.assoc, ← S.map_comp, unop_left_comp_of_mk_le_mk_unop]
          dsimp'
          simp
          
        · exact unop_left_comp_of_mk_le_mk_unop _
          
        · refine' subobject.mk_le_mk_of_comm (subobject.of_mk_le_mk _ _ h).unop.left.op _
          refine' Quiver.Hom.unop_inj _
          have := congr_arg Quiver.Hom.unop (subobject.of_mk_le_mk_comp h)
          simpa [-subobject.of_mk_le_mk_comp] using congr_arg comma_morphism.left this
          )

/-- If `C` is well-copowered and cocomplete and `S` preserves colimits, then
    `costructured_arrow S T` is well-copowered. -/
instance well_copowered_costructured_arrow [WellPowered Cᵒᵖ] [HasColimits C] [PreservesColimits S] :
    WellPowered (CostructuredArrow S T)ᵒᵖ where subobject_small := fun X => small_map (quotientEquiv (unop X)).toEquiv

end CostructuredArrow

end CategoryTheory

