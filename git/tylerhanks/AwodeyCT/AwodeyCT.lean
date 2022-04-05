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
  preserve_units : ∀ {A : C}, hom_map (Category.id A) = Category.id (ob_map A)
  preserve_comp : ∀ {X Y Z : C} (f : hom X Y) (g : hom Y Z),
    hom_map (comp f g) = comp (hom_map f) (hom_map g)

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

def endo_one : functor One One := {
  ob_map := fun _ => one,
  hom_map := fun _ => OneId.mk one one,
  preserve_units := by
    simp
    rfl
  preserve_comp := by
    simp
    intros
    rfl
}

#check endo_one
#eval endo_one.ob_map one

def functor_to_one (C : Type u) [Category C] : (functor C One) := { 
  ob_map := fun _ => one, 
  hom_map := fun _ => OneId.mk one one
  preserve_units := by
    simp
    rfl
  preserve_comp := by
    simp
    intros
    rfl  
}

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

section PreorderCats

class Preorder (Ob : Type u) where
  leq : Ob → Ob → Prop
  leq_ref : ∀ a : Ob, leq a a
  leq_trans : ∀ a b c : Ob, (leq a b) → (leq b c) → (leq a c)
  --leq_decidable : ∀ a b : Ob, Decidable (leq a b)

instance NatPreorder : Preorder Nat where
  leq := Nat.le
  leq_ref := by simp 
  leq_trans := by 
    simp
    apply Nat.le_trans
  /-leq_decidable a b := by
    simp
    apply Nat.decLe-/

instance NatMod4Preorder : Preorder Nat where
  leq a b := a / 4 ≤ b / 4
  leq_ref := by simp
  leq_trans a b c := by
    simp
    apply Nat.le_trans
  /-leq_decidable a b := by
    simp
    apply Nat.decLe-/

#check Nat.le

--def eval_leq (a b : α) (leq : α → α → Prop) : Bool :=
  --let p := leq a b

--#check NatPreorder.leq

--#eval NatPreorder.leq 3 0 -- false
--#eval NatMod4Preorder.leq 3 0 -- true

--structure monotone_map (C : Type u₁) (D : Type u₂) [Preorder C] [Preorder D] where

structure bottom (C : Type u) (P : Preorder C) where
  el : C
  is_bottom : ∀ x : C, P.leq el x

structure top (C : Type u) (P : Preorder C) where
  el : C
  is_top : ∀ x : C, P.leq x el

def nat_bottom : bottom Nat NatMod4Preorder := {
  el := 0
  is_bottom := by
    intro x
    --show 0 / 4 ≤ x / 4
    apply Nat.zero_le
}

#check nat_bottom

structure join (C : Type u) (a b : C) (P : Preorder C) where
  j : C
  upper_bound : (P.leq a j) ∧ (P.leq b j)
  least: ∀ x : C, (P.leq a x) → (P.leq b x) → (P.leq j x)

structure has_all_joins (C : Type u) (P : Preorder C) where
  pf : ∀ (a b : C), ∃ (j : C),
    (P.leq a j) ∧ (P.leq b j) ∧ (∀ x : C, (P.leq a x) → (P.leq b x) → (P.leq j x))

structure meet (C : Type u) (P : Preorder C) (a b : C) where
  m : C
  lower_bound : (P.leq m a) ∧ (P.leq m b)
  greatest: ∀ x : C, (P.leq x a) → (P.leq x b) → (P.leq x m)

structure has_all_meets (C : Type u) (P : Preorder C) where
  pf : ∀ (a b : C), ∃ (m : C),
    (P.leq m a ∧ P.leq m b) ∧ (∀ x : C, (P.leq x a) → (P.leq x b) → (P.leq x m))
#check Nat.not_le_eq
def nat_meet (a b : Nat) : meet Nat NatPreorder a b := {
  m := if a ≤ b then a else b
  lower_bound := by
    apply And.intro
    case left =>
      split
      case inl h =>
        apply Nat.le_refl
      case inr h =>
        rw [Nat.not_le_eq] at h
        revert h
        apply Nat.le_of_succ_le
    case right =>
      split
      case inl h =>
        exact h
      case inr h =>
        apply Nat.le_refl
  greatest := by
    intros x xle_a xle_b
    split
    case inl h =>
      exact xle_a
    case inr h =>
      exact xle_b
}

#eval (nat_meet 5 6).m

theorem nat_all_meets : has_all_meets Nat NatPreorder := {
  pf := by
    intros a b
    let m := nat_meet a b
    exists m.m
    apply And.intro
    case left =>
      exact m.lower_bound
    case right =>
      exact m.greatest
}

def natmod4_meet (a b : Nat) : meet Nat NatMod4Preorder a b := {
  m := if a ≤ b then a else b
  lower_bound := by
    apply And.intro
    case left =>
      split
      case inl h =>
        apply Nat.le_refl
      case inr h =>
        show b / 4 ≤ a / 4
        rw [Nat.not_le_eq] at h
        apply Nat.le_of_succ_le
        rw [← Nat.succ_eq_add_one] at h
        sorry
    case right =>
      split
      case inl h =>
        show a / 4 ≤ b / 4
        sorry
      case inr h =>
        sorry
  greatest := by
    intros x xle_a xle_b
    split
    case inl h =>
      exact xle_a
    case inr h =>
      exact xle_b
}

theorem natmod4_all_meets : has_all_meets Nat NatMod4Preorder := {
  pf := by
    intros a b
    let m := natmod4_meet a b
    exists m.m
    apply And.intro
    case left =>
      exact m.lower_bound
    case right =>
      exact m.greatest
}

/-theorem bottom_implies_all_meets : ∀ (C : Type u) [P : Preorder C],
  (bottom C P) → (has_all_meets C P) := by
    intros C P bot
    induction bot

    constructor
    intros a b-/

end PreorderCats

-- Heyting algebra of propositional provability 
section IPL

/-inductive typ where
  | ttrue
  | tfalse-/

inductive prop where
  | T : prop
  | F : prop
  --| var : String → prop
  | p_or : prop → prop → prop
  | p_and : prop → prop → prop
  | p_impl : prop → prop → prop

open prop
def Γ_t := List (prop × Bool)
section
set_option hygiene false
local notation:10 Γ " ⊢ " p " : " b => judgement Γ p b

inductive judgement : Γ_t → prop → Bool → Prop where
  | true_i : ∀ Γ : Γ_t, Γ ⊢ T : true
  | and_i : ∀ (Γ : Γ_t) (A B : prop), 
      (Γ ⊢ A : true) → (Γ ⊢ B : true) → (Γ ⊢ (p_and A B) : true)
  | and_e1 : ∀ (Γ : Γ_t) (A B : prop),
      (Γ ⊢ (p_and A B) : true) → (Γ ⊢ A : true)
  | and_e2 : ∀ (Γ : Γ_t) (A B : prop),
      (Γ ⊢ (p_and A B) : true) → (Γ ⊢ B : true)
  | impl_i : ∀ (Γ : Γ_t) (A B : prop),
      ((A, true)::Γ ⊢ B : true) → (Γ ⊢ (p_impl A B) : true)
  | impl_e : ∀ (Γ : Γ_t) (A B : prop),
      (Γ ⊢ (p_impl A B) : true) → (Γ ⊢ A : true) → (Γ ⊢ B : true)
  | false_e : ∀ (Γ : Γ_t) (A : prop), (Γ ⊢ F : true) → (Γ ⊢ A : true)
  | or_i1 : ∀ (Γ : Γ_t) (A B : prop), (Γ ⊢ A : true) → (Γ ⊢ (p_or A B) : true)
  | or_i2 : ∀ (Γ : Γ_t) (A B : prop), (Γ ⊢ B : true) → (Γ ⊢ (p_or A B) : true)
  | or_e : ∀ (Γ : Γ_t) (A B C : prop),
      (Γ ⊢ (p_or A B) : true) → 
      ((A, true)::Γ ⊢ C : true) → 
      ((B, true)::Γ ⊢ C : true) → (Γ ⊢ C : true)

  -- structural rules
  | entailment_refl : ∀ (Γ : Γ_t) (A : prop), (A, true)::Γ ⊢ A : true

end

notation:10 Γ " ⊢ " p " : " b => judgement Γ p b



instance : Preorder prop where
  leq A B := ∀ Γ : Γ_t, Γ ⊢ (p_impl A B) : true
  leq_ref := by
    intro A Γ
    apply judgement.impl_i
    apply judgement.entailment_refl
  leq_trans := by
    intro A B C h1 h2 Γ
    apply judgement.impl_i
    let h1 := h1 Γ
    --let h2 := h2 Γ
    apply judgement.impl_i h1









end IPL

section AlgCorrectness

#check Applicative
def list_max (l : List Nat) : Nat := 
  List.foldl (fun (max el : Nat) => if max ≤ el then el else max) 0 l

#eval list_max [5,7,12,2,4]

end AlgCorrectness
