import Mynat.Ineq

structure myint where
  x : mynat
  y : mynat
  deriving Repr

-- The approach is that we define ℤ by the following quotient:
-- ℕ × ℕ ⧸ ∼
-- ∼ = {((a, b), (c, d)) ∈ (ℕ × ℕ)² : a + d = b + c} 

namespace myint

def myequal (a b : myint) : Prop :=
  (a.x + b.y) = (a.y + b.x)

def myintofnat (n : Nat) :=
  myint.mk (mynat.myofnat n) 0

instance : OfNat myint n where
  ofNat := myintofnat n

def toInt (n : myint) :=
  (n.x : Int) - (n.y : Int)

instance : Coe myint Int where
  coe := toInt

#check Quot myequal

-- The following section proves that myequal is an equivalence relation,
-- which means refl, symm and trans hold.

theorem refl (a : myint) : myequal a a := by
  rw [myequal]
  rw [mynat.add_comm]

theorem symm {a b : myint} (hab : myequal a b) : myequal b a := by
  rw [myequal]
  apply Eq.symm
  rw [myequal] at hab
  rw [mynat.add_comm]
  rw [mynat.add_comm b.x a.y]
  exact hab

theorem trans {a b c : myint} (hab : myequal a b) (hbc : myequal b c) : myequal a c := by
  rw [myequal] at hab hbc ⊢
  have hsum := (calc
    a.x + b.y + (b.x + c.y) = a.y + b.x + (b.y + c.x) := by rw [hab, hbc]
  )
  rw [← mynat.add_assoc _ b.x c.y] at hsum
  rw [mynat.add_assoc a.x b.y _] at hsum
  rw [mynat.add_comm b.y b.x] at hsum
  rw [mynat.add_comm a.x _] at hsum
  rw [← mynat.add_assoc (a.y + b.x) b.y c.x] at hsum
  rw [mynat.add_assoc a.y _ _] at hsum
  rw [mynat.add_comm a.y _] at hsum
  rw [mynat.add_assoc (b.x + b.y) _ _] at hsum
  rw [mynat.add_assoc (b.x + b.y) _ _] at hsum
  exact mynat.add_left_cancel (b.x + b.y) _ _ hsum

instance : Equivalence myequal where
  refl := refl
  symm := symm
  trans := trans

instance : HasEquiv myint where
  Equiv := myequal

theorem equiv_is_myequal (a b : myint) : a ≈ b ↔ myequal a b := Iff.rfl
axiom equal_is_xyequal (a b : myint) : a = b ↔ a.x = b.x ∧ a.y = b.y
theorem equal_implies_equiv (a b : myint) : a = b → a ≈ b := by
  intro hab
  rw [equiv_is_myequal]
  rw [myequal]
  rw [hab]
  rw [mynat.add_comm]

theorem destruct_x (ax ay : mynat) : ({ x := ax, y := ay } : myint).x = ax := rfl
theorem destruct_y (ax ay : mynat) : ({ x := ax, y := ay } : myint).y = ay := rfl

theorem default_nat_has_no_y (n : Nat) : (@OfNat.ofNat myint n instOfNatMyint).y = 0 := by
  rw [OfNat.ofNat, instOfNatMyint, myintofnat]

theorem default_nat_has_same_x (n : Nat) : (@OfNat.ofNat myint n instOfNatMyint).x = mynat.myofnat n := by
  rw [OfNat.ofNat, instOfNatMyint, myintofnat]

def mynotequal (a b : myint) : Prop := 
  (a.x + b.y) ≠ (a.y + b.x)

infix:50 " ≉  " => mynotequal

theorem nequiv_iff_not_equiv (a b : myint) : a ≉ b ↔ ¬ (a ≈ b) := by
  apply Iff.intro
  . intro h
    rw [mynotequal] at h
    rw [equiv_is_myequal, myequal]
    exact h
  . intro h
    rw [equiv_is_myequal, myequal] at h
    rw [mynotequal]
    exact h

end myint