def hello := "world"

universe v u u₁ u₂
#check Sort 0
class Category (Ob : Type u) where
  hom : Ob → Ob → Sort v
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

section CatMonoid

class Monoid (α : Type u) where
  unit : α
  op : α → α → α
  op_assoc: ∀ a b c : α, op a (op b c) = op (op a b) c
  l_unit : ∀ a : α, op unit a = a
  r_unit : ∀ a : α, op a unit = a

instance cat_of_monoid (α : Type u) (M : Monoid α) : Category Unit where
  hom := fun (_ _ : Unit) => α
  id := fun (x : Unit) => M.unit
  comp := fun (f g : α) => M.op f g
  comp_assoc := by simp; intros; apply M.op_assoc
  l_unit := by simp; intros; apply M.l_unit
  r_unit := by simp; intros; apply M.r_unit
     
instance NatsUnderPlus : Monoid Nat where
  unit := 0
  op x y := x + y
  l_unit x := by simp
  r_unit x := by simp
  op_assoc a b c := by
    simp
    rw [Nat.add_assoc]

def NatsUnderPlusCat := cat_of_monoid Nat NatsUnderPlus

-- TODO: Figure out how to evaluate homs in these categories

end CatMonoid

section PreorderCats

class Preorder (Ob : Type u) where
  leq : Ob → Ob → Prop
  leq_ref : ∀ a : Ob, leq a a
  leq_trans : ∀ a b c : Ob, (leq a b) → (leq b c) → (leq a c)

-- Construct a thin category from a preorder
instance cat_of_preorder (α : Type u) (P : Preorder α) : Category.{0} α where
  hom := P.leq
  id a := by apply P.leq_ref
  comp := by apply P.leq_trans 
  comp_assoc := by intros; rfl
  l_unit := by intros; rfl
  r_unit := by intros; rfl

-- Examples

instance NatPreorder : Preorder Nat where
  leq := Nat.le
  leq_ref := by simp 
  leq_trans := by 
    simp
    apply Nat.le_trans

instance NatMod4Preorder : Preorder Nat where
  leq a b := a / 4 ≤ b / 4
  leq_ref := by simp
  leq_trans a b c := by
    simp
    apply Nat.le_trans

-- Top and Bottom

structure bottom (C : Type u) (P : Preorder C) where
  el : C
  is_bottom : ∀ x : C, P.leq el x

structure top (C : Type u) (P : Preorder C) where
  el : C
  is_top : ∀ x : C, P.leq x el

-- Can set el to 0-3 and this will hold because 0-3 are isomorphic in this preorder
def nat_bottom : bottom Nat NatMod4Preorder := {
  el := 0
  is_bottom := by
    intro x
    apply Nat.zero_le
}

#check nat_bottom

-- Meets and joins. TODO: restate these as degenerate cases of products/co-products in thin cats

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

-- examples

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

-- TODO: get rid of sorrys :(
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

end PreorderCats

-- Category of Binary relations between types
section CatRel

def rel := Type u
--instance : inhabited rel := by unfold rel;

instance Rel : Category (Type u) where
  hom A B := A → B → Prop
  id A := fun (a b : A) => a = b
  comp := fun R S a c => ∃ b, R a b ∧ S b c
  comp_assoc := by
    simp
    intro A B C D f g h
    --have a : A. TODO: I think this proof requires that types are inhabited
    sorry
  l_unit := by
    simp
    intro A B f
    sorry
  r_unit := by
    sorry 

end CatRel

-- Heyting algebra of propositional provability 
section IPL

inductive prop where
  | T : prop
  | F : prop
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
  --TODO: Use this more proper definition of transitivity (needs weakening to apply)
  --| entailment_trans : ∀ (Γ₁ Γ₂ : Γ_t) (A B : prop),
      --(Γ₁ ⊢ A : true) → ((A, true)::Γ₂ ⊢ B : true) → ((List.append Γ₁ Γ₂) ⊢ B : true)
  | entailment_trans : ∀ (Γ : Γ_t) (A B C : prop),
      ((A, true)::Γ ⊢ B : true) → ((B, true)::Γ ⊢ C : true) → ((A, true)::Γ ⊢ C : true)

end

notation:10 Γ " ⊢ " p " : " b => judgement Γ p b

axiom impl_inversion : ∀ (Γ : Γ_t) (A B : prop), 
  (Γ ⊢ (p_impl A B) : true) → ((A, true)::Γ ⊢ B : true)

instance : Preorder prop where
  leq A B := ∀ Γ : Γ_t, Γ ⊢ (p_impl A B) : true
  leq_ref := by
    intro A Γ
    apply judgement.impl_i
    apply judgement.entailment_refl
  leq_trans := by
    intro A B C h1 h2 Γ
    apply judgement.impl_i
    let h1 := impl_inversion Γ A B (h1 Γ)
    let h2 := impl_inversion Γ B C (h2 Γ)
    apply judgement.entailment_trans Γ A B C h1 h2

end IPL

section AlgCorrectness

def list_max (l : List Nat) : Nat := 
  List.foldl (fun (max el : Nat) => if max ≤ el then el else max) 0 l

#eval list_max [5,7,12,2,4]

end AlgCorrectness
