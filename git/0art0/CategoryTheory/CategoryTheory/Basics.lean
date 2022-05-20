namespace CategoryTheory

structure Category where
  ob : Type _
  hom : ob → ob → Type _
  id : {A : ob} → hom A A
  comp : {A B C : ob} → hom A B → hom B C → hom A C

  compAssoc : {A B C D : ob} → {f : hom A B} → {g : hom B C} → {h : hom C D} →
              comp f (comp g h) = comp (comp f g) h
  leftId : {A B : ob} → {f : hom A B} →
           comp id f = f
  rightId : {A B : ob} → {f : hom A B} →
            comp f id = f

def Typ : Category :=
  {
    ob := Type,
    hom := λ (A B : Type) => (A → B),
    id := id,
    comp := λ f g => g ∘ f,

    compAssoc := by intros; rfl,
    leftId := by intros; rfl,
    rightId := by intros; rfl
  }

structure Functor (C D : Category) where
  Θ : C.ob → D.ob
  ϕ : {A B : C.ob} → (f : C.hom A B) → D.hom (Θ A) (Θ B)

  idMap : {A : C.ob} → (ϕ (C.id : C.hom A A) = D.id)
  compMap : {X Y Z : C.ob} → (f : C.hom X Y) → (g : C.hom Y Z) →
            ϕ (C.comp f g) = D.comp (ϕ f) (ϕ g)

structure NaturalTransformation {C D : Category} (F G : Functor C D) where
  component : (X : C.ob) → D.hom (F.Θ X) (G.Θ X)
  commutingSquare : {X Y : C.ob} → (f : C.hom X Y) →
                    D.comp (component X) (G.ϕ f) = D.comp (F.ϕ f) (component Y)

def Functor.Id {C : Category} : Functor C C :=
  {
   Θ := id,
   ϕ := id,

   idMap := by intros; rfl,
   compMap := by intros; rfl
  }

def Functor.comp {C D E : Category} (F : Functor C D) (G : Functor D E) : Functor C E :=
  {
    Θ := G.Θ ∘ F.Θ,
    ϕ := G.ϕ ∘ F.ϕ,

    idMap := by intros; simp; rw [F.idMap, G.idMap]
    compMap := by intros; simp; rw [F.compMap, G.compMap]
  }

def Cat : Category :=
  {
    ob := Category,
    hom := Functor,
    id := Functor.Id,
    comp := Functor.comp,

    compAssoc := by intros; simp [Functor.comp]; apply And.intro <;> rfl,
    leftId := by intros; rfl,
    rightId := by intros; rfl
  }

def NaturalTransformation.Id {C D : Category} {F : Functor C D} : NaturalTransformation F F :=
  {
    component := λ X => D.id,
    commutingSquare := by intros; simp [D.leftId, D.rightId]
  }

def NaturalTransformation.comp {C D : Category} {F G H : Functor C D}
                                (η₁ : NaturalTransformation F G) (η₂ : NaturalTransformation G H) :
                                NaturalTransformation F H :=
{
  component := λ X => D.comp (η₁.component X) (η₂.component X),
  commutingSquare := by intros; simp; rw [D.compAssoc, ← η₁.commutingSquare, ← D.compAssoc, η₂.commutingSquare, D.compAssoc]
}

structure Iso (A : Type _) (B : Type _) where
  fwd : A → B
  bck : B → A
  fstId : bck ∘ fwd = id
  sndId : fwd ∘ bck = id

end CategoryTheory
