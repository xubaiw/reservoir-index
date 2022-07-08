import Myint.Add

namespace myint

def myneg (m : myint) : myint :=
  myint.mk m.y m.x

instance : Neg myint where
  neg := myneg

theorem neg_eq_myneg (m : myint) : -m = myneg m := rfl

def mysub (m n : myint) : myint :=
  m + myneg n

instance : Sub myint where
  sub := mysub

theorem sub_eq_mysub (m n : myint) : m - n = mysub m n := rfl
theorem sub_eq_plusneg (m n : myint) : m - n = m + (-n) := rfl

-- This proves that -m is an additive inverse of m and an identity is 0.
theorem neg_is_inv (m : myint) : m + (-m) ≈ 0 := by
  rw [neg_eq_myneg]
  rw [equiv_is_myequal]
  rw [myneg]
  rw [myequal]
  rw [add_x, add_y]
  rw [destruct_x m.y m.x]
  rw [destruct_y m.y m.x]
  rw [mynat.add_comm m.x m.y]
  rw [zerox, zeroy]

theorem negneg_eq_self (m : myint) : -(-m) ≈ m := by
  rw [neg_eq_myneg]
  rw [neg_eq_myneg]
  rw [equiv_is_myequal]
  rw [myneg]
  rw [myneg]
  rw [destruct_y]
  rw [destruct_x m.y m.x]
  rw [myequal]
  rw [destruct_x]
  rw [destruct_y]
  rw [mynat.add_comm]

example : (5 : myint) - (2 : myint) ≈ (3 : myint) := by
  have : (3 : myint) ≈ (3 : myint) := rfl
  have : (3 : myint) ≈ (3 : myint) + (0 : myint) := rfl
  have : (3 : myint) ≈ (3 : myint) + (2 - 2 : myint) := by
    rw [sub_eq_plusneg]
    have htinv : 0 ≈ (2 + -2) := symm (neg_is_inv 2)
    have hleft : 3 + 0 ≈ 3 + (2 + -2) := add_left 3 0 (2 + -2) htinv
    have happ : 3 ≈ (3 + (2 + -2)) := trans this hleft
    exact happ
  rw [sub_eq_plusneg] at this
  have htrans : 3 ≈ (3 + 2 + -2) := trans
    this
    (symm (add_assoc (3 : myint) (2 : myint) (-2 : myint)))
  have : (3 : myint) + (2 : myint) ≈ (5 : myint) := by
    apply if_x_and_y_equal_then_equiv
    rw [add_x]
    rw [add_y]
    apply And.intro
    case a.left =>
      repeat rw [default_nat_has_same_x]
      repeat rw [mynat.myofnat]
      rw [mynat.mynat_zero_eq_zero]
      repeat rw [mynat.add_succ]
      rw [mynat.add_zero]
    case a.right =>
      repeat rw [default_nat_has_no_y]
      rfl
  have : (3 : myint) + (2 : myint) + (-2 : myint) ≈ (5 : myint) + (-2 : myint) :=
    (add_right _ _ (-2)) this
  have : (3 : myint) ≈ (5 : myint) + (-2 : myint) := trans htrans this
  have : (5 : myint) + (-2 : myint) ≈ (3 : myint) := symm this
  rw [equiv_is_myequal]
  rw [sub_eq_plusneg]
  exact this

theorem sub_right (a b t : myint) : a ≈ b → a - t ≈ b - t := by
  rw [sub_eq_plusneg]
  exact add_right a b (-t)

theorem add_right_cancel (a t b : myint) : a + t ≈ b + t → a ≈ b := by
  intro h
  have hmt := add_right (a+t) (b+t) (-t) h
  have hassoc := symm (add_assoc a t (-t))
  rw [← equiv_is_myequal] at hassoc
  have ha := trans hassoc hmt
  rw [← equiv_is_myequal] at ha
  have hb := trans ha (add_assoc b t (-t))
  rw [← equiv_is_myequal] at hb
  have hni := neg_is_inv t
  have hb0 := trans hb (add_left b (t + -t) 0 hni)
  rw [← equiv_is_myequal] at hb0
  have hb1 := trans hb0 (add_zero b)
  rw [← equiv_is_myequal] at hb1
  have ha0 := trans (symm (add_left a (t + -t) 0 hni)) hb1
  have ha1 := symm ha0
  have ha2 := trans ha1 (add_zero a)
  exact symm ha2

theorem add_left_cancel (t a b : myint) : t + a ≈ t + b → a ≈ b := by
  have hhelp := add_right_cancel a t b
  intro h
  have := trans (trans (add_comm a t) h) (add_comm t b)
  exact hhelp this

theorem add_right_cancel_iff (t a b : myint) : a + t ≈ b + t ↔ a ≈ b := by
  apply Iff.intro
  . exact add_right_cancel a t b
  . intro h
    exact add_right a b t h

end myint