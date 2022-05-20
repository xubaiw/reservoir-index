import CategoryTheory.Basics

namespace CategoryTheory

def dual (C : Category) : Category :=
  {
    ob := C.ob,
    hom := λ A B => C.hom B A,
    id := C.id,
    comp := λ f g => C.comp g f,

    compAssoc := by intros; simp [C.compAssoc]
    leftId := by intros; simp [C.rightId],
    rightId := by intros; simp [C.leftId]
  }

def list : Functor Typ Typ :=
  {
    Θ := List,
    ϕ := List.map,

    idMap := by
      intros
      apply funext
      intro l
      induction l with
        | nil => rfl
        | cons h t ih => simp [List.map, ih]; rfl
      ,
    compMap := by
      intros
      apply funext
      intro l
      induction l with
        | nil => rfl
        | cons h t ih => simp [List.map, ih]; rfl
  }

def Hom_ {C : Category} (A : C.ob) : Functor C Typ :=
  {
    Θ := C.hom A,
    ϕ := λ f => λ g => C.comp g f,

    idMap := by intros; apply funext; intro; simp; rw [C.rightId]; rfl,
    compMap := by intros; simp; apply funext; intro; rw [Category.compAssoc]; rfl
  }

def _Hom {C : Category} (A : C.ob) : Functor (dual C) Typ :=
  {
    Θ := λ X => C.hom X A,
    ϕ := λ f => λ g => C.comp f g,

    idMap := by
          intros; apply funext; intro; simp
          show C.comp C.id _ = Typ.id _; rw [C.leftId]; rfl
    compMap := by
        intros; apply funext; intro; simp;
        show C.comp (C.comp _ _) _ = Typ.comp (λ g => C.comp _ g) (λ g => C.comp _ g) _; rw [← C.compAssoc]; rfl
  }

def FunctorCategory (C D : Category) : Category :=
  {
    ob := Functor C D,
    hom := NaturalTransformation,
    id := NaturalTransformation.Id,
    comp := NaturalTransformation.comp,

    compAssoc := by intros; simp [NaturalTransformation.comp]; apply funext; intro; simp [D.compAssoc]
    leftId := by
      intros F G η; cases η;
      simp [NaturalTransformation.Id, NaturalTransformation.comp]; apply funext; intro; rw [D.leftId]
    rightId := by
      intros F G η; cases η;
      simp [NaturalTransformation.Id, NaturalTransformation.comp]; apply funext; intro; rw [D.rightId]
  }

end CategoryTheory
