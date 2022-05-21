import CategoryTheory.Basics
import CategoryTheory.Constructions

namespace CategoryTheory

def cov_yoneda {C : Category} (F : Functor C Typ) (A : C.ob) : Iso (NaturalTransformation (Hom_ A) F) (F.Θ A) :=
  {
    fwd := by
      intro η
      apply η.component
      exact C.id
    bck := by
      intro a
      exact
        {
          component := by
            intro X
            intro f
            apply F.ϕ f
            exact a
          commutingSquare := by
            intro X Y f
            apply funext
            intro x
            show (F.ϕ f) (F.ϕ x a) = F.ϕ (C.comp x f) a
            rw [Functor.compMap]
            rfl
        }
    fstId := by
      apply funext
      intro ⟨cmp, sq⟩
      simp
      apply funext
      intro Y
      apply funext
      intro f
      have : F.ϕ f (cmp A C.id) = cmp Y (C.comp C.id f) := congrFun (@sq A Y f) (C.id)
      rw [C.leftId] at this
      assumption
    sndId := by
      apply funext
      intro
      simp
      rw [Functor.idMap]
      rfl
  }

def contr_yoneda {C : Category} (F : Functor (dual C) Typ) (A : C.ob) : Iso (NaturalTransformation (_Hom A) F) (F.Θ A) :=
  {
    fwd := by
      intro η
      apply η.component
      exact C.id
    bck := by
      intro a
      exact
      {
        component := by
          intro X
          intro f
          apply F.ϕ f
          exact a
        commutingSquare := by
          intro f
          intro Y
          intro g
          apply funext
          intro x
          show (F.ϕ g (F.ϕ x a)) = F.ϕ ((dual C).comp x g) a
          rw [Functor.compMap]
          rfl
      }
    fstId := by
      apply funext
      intro ⟨cmp, sq⟩
      simp
      apply funext
      intro Y
      apply funext
      intro f
      have : F.ϕ f (cmp A C.id) = cmp Y ((dual C).comp (dual C).id f) := congrFun (@sq A Y f) (C.id)
      rw [(dual C).leftId] at this
      assumption
    sndId := by
      apply funext
      intro a
      simp
      show F.ϕ (dual C).id a = a
      rw [Functor.idMap]
      rfl
  }


def yoneda_embedding {C : Category} (A B : C.ob) : Iso (NaturalTransformation (_Hom A) (_Hom B)) (C.hom A B) :=
  contr_yoneda (_Hom B) A

end CategoryTheory
