def hello := "world"

universe v u u₁ u₂

class Category (Ob : Type u) where
  hom : Ob → Ob → Type v
  id : ∀ A : Ob, hom A A
  comp : ∀ {A B C : Ob}, (hom A B) → (hom B C) → (hom A C)
  comp_assoc : ∀ {A B C D : Ob} (f : hom A B) (g : hom B C) (h : hom C D),
    comp f (comp g h) = comp (comp f g) h
  l_unit : ∀ {A B : Ob} (f : hom A B), comp (id A) f = f
  r_unit : ∀ {A B : Ob} (f : hom A B), comp f (id B) = f

export Category (hom id comp)

structure functor (C : Type u₁) (D : Type u₂) [Category C] [Category D] where
  ob_map : C → D
  hom_map : ∀ {A B : C}, (hom A B) → (hom (ob_map A) (ob_map B))

#check functor

section CategoryOne

inductive One where
  | one : One

inductive OneId where
  | mk : One → One → OneId

instance : ToString One where
  toString one := "•"

instance : ToString OneId where
  toString _ := "id•"

open One

instance : Category One where
  hom (X Y : One) := OneId
  id _ := OneId.mk one one
  comp := fun (OneId.mk one one) (OneId.mk one one) => OneId.mk one one
  comp_assoc f g h := by simp
  l_unit f := by simp
  r_unit f := by simp

#eval Category.id one
#eval comp (Category.id one) (Category.id one)
#check { ob_map := fun x => one, hom_map := fun x => OneId.mk one one : functor One One }

def functor_to_one (C : Type u) [Category C] : (functor C One) :=
    { ob_map := fun _ => one, hom_map := fun _ => OneId.mk one one : functor C One }

end CategoryOne

-- The category of Lean types (in universe 1) and functions between them
section LeanCat

instance : Category Type where
  hom (X Y : Type) := X → Y
  id A := fun (x : A) => x
  comp f g := fun x => g (f x)
  comp_assoc f g h := by simp
  l_unit f := by simp
  r_unit f := by simp

def list_length (l : List Nat) : Nat :=
  match l with
  | x::xs => 1 + (list_length xs)
  | nil => 0

#eval list_length [1,2,3,4]

def double (x : Nat) : Nat := x * 2

#eval (Category.id Nat) 7
#eval (Category.id (List Nat)) [1,2,3]


def doubleH := Category.comp (Category.id Nat) double
def lengthH := Category.comp (Category.id (List Nat)) list_length

#check comp lengthH doubleH
#eval (comp lengthH doubleH) [1,2,3,4]

def F := functor_to_one Type
#check F

#eval F.ob_map Nat
#eval F.hom_map lengthH

end LeanCat

/-section CategoryTwo

inductive Two where
  | one : Two
  | two : Two

open Two
#check Two
instance : Category Two where
  hom := fun (X Y : Two) => Two → Two
  id := fun (A : Two) => id
  comp := fun (A B C: Two) (f : hom A B) (g : hom B C) => fun (x : Two) => g B C (f A B x)

end CategoryTwo-/

section CatMonoid

class Monoid (α : Type u) where
  unit : α
  op : α → α → α
  op_assoc: ∀ a b c : α, op (op a b) c = op a (op b c)
  l_unit : ∀ a : α, op unit a = a
  r_unit : ∀ a : α, op a unit = a

instance : Monoid Nat where
  unit := 0
  op x y := x + y
  l_unit x := by simp
  r_unit x := by simp
  op_assoc a b c := by
    simp
    rw [Nat.add_assoc]

end CatMonoid
