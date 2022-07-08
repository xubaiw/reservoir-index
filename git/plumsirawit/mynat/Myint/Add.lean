import Myint.Base

namespace myint

def myadd (m n : myint) : myint :=
  myint.mk (m.x + n.x) (m.y + n.y)

instance : Add myint where
  add := myadd

theorem add_eq_myadd (m n : myint) : m + n = myadd m n := rfl

theorem add_x (m n : myint) : (m + n).x = m.x + n.x := by
  rw [add_eq_myadd]
  rw [myadd]

theorem add_y (m n : myint) : (m + n).y = m.y + n.y := by
  rw [add_eq_myadd]
  rw [myadd]

theorem zerox : (0 : myint).x = 0 := rfl
theorem zeroy : (0 : myint).y = 0 := rfl

theorem add_zero (m : myint) : m + 0 ≈ m := by
  rw [equiv_is_myequal]
  rw [myequal]
  rw [add_x, add_y]
  rw [zerox, zeroy]
  rw [mynat.add_zero]
  rw [mynat.add_zero]
  exact mynat.add_comm m.x m.y

theorem zero_add (n : myint) : (0 + n) ≈ n := by
  rw [equiv_is_myequal]
  rw [myequal]
  rw [add_eq_myadd]
  rw [myadd]
  rw [zerox, zeroy]
  rw [mynat.zero_add]
  rw [mynat.zero_add]
  rw [mynat.add_comm]

theorem if_x_and_y_equal_then_equiv (a b : myint) : a.x = b.x ∧ a.y = b.y → a ≈ b := by
  intro h
  rw [equiv_is_myequal]
  rw [myequal]
  rw [h.left]
  rw [h.right]
  rw [mynat.add_comm]

theorem add_assoc (a b c : myint) : (a + b) + c ≈ a + (b + c) := by
  rw [equiv_is_myequal]
  rw [myequal]
  apply if_x_and_y_equal_then_equiv
  apply And.intro
  case a.left =>
    rw [add_x]
    rw [add_x]
    rw [add_x]
    rw [add_x]
    rw [mynat.add_assoc]
  case a.right =>
    rw [add_y]
    rw [add_y]
    rw [add_y]
    rw [add_y]
    rw [mynat.add_assoc]

theorem add_comm (a b : myint) : a + b ≈ b + a := by
  apply if_x_and_y_equal_then_equiv
  apply And.intro
  . rw [add_x]
    rw [add_x]
    rw [mynat.add_comm]
  . rw [add_y]
    rw [add_y]
    rw [mynat.add_comm]

attribute [simp] add_assoc add_comm

theorem add_right (a b t : myint) : a ≈ b → a + t ≈ b + t := by
  intro h
  rw [equiv_is_myequal] at h ⊢ 
  rw [myequal] at h ⊢
  rw [add_x]
  rw [add_y]
  rw [add_y]
  rw [add_x]
  rw [← mynat.add_assoc (a.x + t.x) _ _]
  rw [mynat.add_assoc a.x t.x]
  rw [mynat.add_comm t.x b.y]
  rw [← mynat.add_assoc a.x _]
  rw [← mynat.add_assoc (a.y + t.y)]
  rw [mynat.add_assoc a.y]
  rw [mynat.add_comm t.y]
  rw [← mynat.add_assoc]
  rw [h]
  rw [mynat.add_assoc (a.y + b.x)]
  rw [mynat.add_comm t.x]
  rw [← mynat.add_assoc]

theorem add_left (t a b : myint) : a ≈ b → t + a ≈ t + b := by
  intro h
  have := add_right a b t h
  have := trans (add_comm t a) this
  exact trans this (add_comm b t)

theorem add_equiv (a b c d : myint) : a ≈ b ∧ c ≈ d → a + c ≈ b + d := by
  intro h
  have h1 := And.left h
  have h2 := And.right h
  have hac := add_right a b c h1
  have hbd := add_left b c d h2
  exact trans hac hbd

theorem ne_add_still_ne (a b t : myint) : a ≉  b → a + t ≉  b + t := by
  intro h
  rw [mynotequal] at h ⊢
  repeat rw [add_eq_myadd, myadd]
  rw [destruct_x, destruct_y]
  rw [destruct_y _ (a.y + t.y), destruct_x (b.x + t.x) _]
  rw [← mynat.add_assoc]
  rw [mynat.add_assoc a.x]
  rw [mynat.add_comm t.x]
  rw [← mynat.add_assoc]
  rw [← mynat.add_assoc]
  rw [mynat.add_assoc a.y]
  rw [mynat.add_comm t.y]
  rw [← mynat.add_assoc]
  rw [mynat.add_assoc (a.y + b.x)]
  rw [mynat.add_comm t.y]
  rw [mynat.add_assoc (a.x + b.y)]
  intro h'
  have := (mynat.add_right_cancel_iff (t.x + t.y) (a.x + b.y) (a.y + b.x)).mp h'
  exact h this

end myint