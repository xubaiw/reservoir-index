import Myint.Sub

namespace myint

def mymul (m n : myint) : myint :=
  myint.mk (m.x * n.x + m.y * n.y) (m.x * n.y + m.y * n.x)

instance : Mul myint where
  mul := mymul

theorem mul_eq_mymul (a b : myint) : a * b = mymul a b := rfl
theorem mul_zero (a : myint) : a * 0 ≈ 0 := rfl

theorem zero_mul (m : myint) : 0 * m ≈ 0 := by
  rw [mul_eq_mymul]
  rw [mymul]
  apply if_x_and_y_equal_then_equiv
  apply And.intro
  . rw [destruct_x]
    rw [zerox, zeroy]
    rw [mynat.zero_mul, mynat.zero_mul]
    rfl
  . rw [destruct_y]
    rw [zerox, zeroy]
    rw [mynat.zero_mul, mynat.zero_mul]
    rfl

theorem mul_one (a : myint) : a * 1 ≈ a := by
  rw [mul_eq_mymul]
  rw [mymul]
  rw [default_nat_has_same_x 1]
  rw [default_nat_has_no_y]
  rw [mynat.mul_zero, mynat.mul_zero]
  rw [mynat.add_zero, mynat.zero_add]
  rw [mynat.myofnat, mynat.myofnat]
  rw [mynat.mynat_zero_eq_zero]
  rw [← mynat.one_eq_succ_zero]
  rw [mynat.mul_one, mynat.mul_one]
  apply if_x_and_y_equal_then_equiv
  apply And.intro
  . rw [destruct_x]
  . rw [destruct_y]
  
theorem mul_negone (a : myint) : a * -1 ≈ -a := by
  have hnegonex : (-1 : myint).x = 0 := by
    rw [neg_eq_myneg]
    rw [myneg]
    rw [destruct_x]
    rw [default_nat_has_no_y]
  have hnegoney : (-1 : myint).y = 1 := by
    rw [neg_eq_myneg]
    rw [myneg]
    rw [destruct_y]
    rw [default_nat_has_same_x]
    rw [mynat.myofnat, mynat.myofnat]
    rw [mynat.mynat_zero_eq_zero]
    rfl
  rw [mul_eq_mymul]
  rw [mymul]
  apply if_x_and_y_equal_then_equiv
  apply And.intro
  . rw [destruct_x]
    rw [hnegonex, hnegoney]
    rw [mynat.mul_zero]
    rw [mynat.zero_add]
    rw [mynat.mul_one]
    rw [neg_eq_myneg]
    rw [myneg]
  . rw [destruct_y]
    rw [hnegonex, hnegoney]
    rw [mynat.mul_zero]
    rw [mynat.add_zero]
    rw [mynat.mul_one]
    rw [neg_eq_myneg]
    rw [myneg]

theorem one_mul (m : myint) : 1 * m ≈ m := by
  rw [mul_eq_mymul, mymul]
  rw [default_nat_has_same_x]
  rw [mynat.myofnat, mynat.myofnat, mynat.mynat_zero_eq_zero, ← mynat.one_eq_succ_zero]
  rw [default_nat_has_no_y]
  rw [mynat.zero_mul, mynat.zero_mul]
  rw [mynat.one_mul, mynat.one_mul]
  rw [mynat.add_zero, mynat.add_zero]
  rw [equiv_is_myequal, myequal]
  rw [destruct_x, destruct_y]
  rw [mynat.add_comm]

theorem mul_add (t a b : myint) : t * (a + b) ≈ t * a + t * b := by
  apply if_x_and_y_equal_then_equiv
  apply And.intro
  . rw [mul_eq_mymul, mymul]
    rw [destruct_x]
    rw [add_x, add_y, add_x]
    rw [mul_eq_mymul, mymul]
    rw [destruct_x (t.x * a.x + t.y * a.y) _]
    rw [mul_eq_mymul, mymul]
    rw [destruct_x (t.x * b.x + t.y * b.y) _]
    rw [← mynat.add_assoc]
    rw [mynat.add_assoc (t.x * a.x) _]
    rw [mynat.add_comm (t.y * a.y) _]
    rw [← mynat.add_assoc]
    rw [mynat.mul_add, mynat.mul_add]
    rw [← mynat.add_assoc]
  . rw [mul_eq_mymul, mymul]
    rw [destruct_y]
    rw [add_x, add_y, add_y]
    rw [mul_eq_mymul, mymul]
    rw [destruct_y _ (t.x * a.y + t.y * a.x)]
    rw [mul_eq_mymul, mymul]
    rw [destruct_y _ (t.x * b.y + t.y * b.x)]
    rw [← mynat.add_assoc]
    rw [mynat.add_assoc (t.x * a.y) _]
    rw [mynat.add_comm (t.y * a.x) _]
    rw [← mynat.add_assoc]
    rw [mynat.mul_add, mynat.mul_add]
    rw [← mynat.add_assoc]

theorem mul_assoc (a b c : myint) : (a * b) * c ≈ a * (b * c) := by
  rw [mul_eq_mymul, mul_eq_mymul, mul_eq_mymul, mul_eq_mymul]
  rw [mymul, mymul, mymul, mymul]
  apply if_x_and_y_equal_then_equiv
  apply And.intro
  . rw [destruct_x, destruct_x]
    conv =>
      rhs
      rw [destruct_x]
      congr
      . arg 2
        rw [destruct_x]
      . arg 2
        rw [destruct_y]
    conv =>
      lhs
      arg 2
      arg 1
      rw [destruct_y]
    rw [mynat.add_mul, mynat.add_mul, mynat.mul_add, mynat.mul_add]
    rw [← mynat.mul_assoc, ← mynat.mul_assoc, ← mynat.mul_assoc, ← mynat.mul_assoc]
    conv =>
      rhs
      rw [mynat.add_comm (a.y * b.x * c.y) _]
      rw [← mynat.add_assoc]
      rw [mynat.add_assoc (a.x * b.x * c.x) _ _]
      rw [mynat.add_comm (a.x * b.y * c.y)]
      rw [← mynat.add_assoc]
    rw [← mynat.add_assoc]
  . rw [destruct_x, destruct_y]
    conv =>
      rhs
      rw [destruct_y]
      congr
      . arg 2
        rw [destruct_y]
      . arg 2
        rw [destruct_x]
    conv =>
      lhs
      arg 2
      arg 1
      rw [destruct_y]
    rw [mynat.add_mul, mynat.add_mul, mynat.mul_add, mynat.mul_add]
    rw [← mynat.mul_assoc, ← mynat.mul_assoc, ← mynat.mul_assoc, ← mynat.mul_assoc]
    conv =>
      rhs
      rw [mynat.add_comm (a.y * b.x * c.x) _]
      rw [← mynat.add_assoc]
      rw [mynat.add_assoc (a.x * b.x * c.y) _ _]
      rw [mynat.add_comm (a.x * b.y * c.x)]
      rw [← mynat.add_assoc]
    rw [← mynat.add_assoc]

theorem mul_comm (a b : myint) : a * b ≈ b * a := by
  rw [mul_eq_mymul, mymul, mul_eq_mymul, mymul]
  apply if_x_and_y_equal_then_equiv
  apply And.intro
  . rw [destruct_x, destruct_x (b.x * a.x + b.y * a.y)]
    rw [mynat.mul_comm, mynat.mul_comm a.y _]
  . rw [destruct_y, destruct_y _ (b.x * a.y + b.y * a.x)]
    rw [mynat.mul_comm, mynat.mul_comm a.y _]
    rw [mynat.add_comm]

theorem add_mul (a b t : myint) : (a + b) * t ≈ a * t + b * t := by
  have h1 : (a + b) * t ≈ t * (a + b) := mul_comm (a + b) t
  have h2 : t * (a + b) ≈ t * a + t * b := mul_add t a b
  have h3 : t * a ≈ a * t := mul_comm t a
  have h4 : t * b ≈ b * t := mul_comm t b
  have h5 := add_equiv (t * a) (a * t) (t * b) (b * t) ⟨ h3, h4 ⟩
  exact trans (trans h1 h2) h5

theorem mul_right (a b t : myint) : a ≈ b → a * t ≈ b * t := by
  intro h
  rw [mul_eq_mymul, mul_eq_mymul]
  rw [mymul, mymul]
  rw [equiv_is_myequal, myequal]
  rw [destruct_x]
  rw [destruct_y _ (b.x * t.y + b.y * t.x)]
  rw [destruct_x (b.x * t.x + b.y * t.y) _]
  rw [destruct_y _ (a.x * t.y + a.y * t.x)]
  rw [equiv_is_myequal, myequal] at h
  have htx : (a.x + b.y) * t.x = (a.y + b.x) * t.x := by rw[h]
  have hty : (a.x + b.y) * t.y = (a.y + b.x) * t.y := by rw[h]
  rw [mynat.add_comm (b.x * t.y) _]
  rw [mynat.add_comm (a.x * t.y) _]
  rw [← mynat.add_assoc, ← mynat.add_assoc]
  rw [mynat.add_assoc (a.x * t.x) _]
  rw [mynat.add_comm (a.y * t.y) _]
  rw [← mynat.add_assoc]
  rw [mynat.add_assoc (a.y * t.x) _]
  rw [mynat.add_comm (a.x * t.y) _]
  rw [← mynat.add_assoc]
  rw [← mynat.add_mul, ← mynat.add_mul]
  rw [mynat.add_assoc, ← mynat.add_mul]
  rw [mynat.add_assoc, ← mynat.add_mul]
  rw [htx, hty]

theorem mul_left (t a b : myint) : a ≈ b → t * a ≈ t * b := by
  intro h
  have := mul_right a b t h
  exact trans (trans (mul_comm t a) this) (mul_comm b t)

theorem mul_left_comm (a b c : myint) : a * (b * c) ≈ b * (a * c) := by
  have h1 : a * (b * c) ≈ a * b * c := symm (mul_assoc a b c)
  have h2 : a * b * c ≈ b * a * c := mul_right (a * b) (b * a) c (mul_comm a b)
  have h3 : b * a * c ≈ b * (a * c) := mul_assoc b a c
  exact trans (trans h1 h2) h3

attribute [simp] mul_assoc mul_comm mul_left_comm

theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : myint) (h : a * b ≈ 0) :
  a ≈ 0 ∨ b ≈ 0 := by
  rw [mul_eq_mymul, mymul] at h
  rw [equiv_is_myequal, myequal] at h
  rw [destruct_x, destruct_y _ (a.x * b.y + a.y * b.x)] at h
  rw [zerox, zeroy] at h
  repeat rw [mynat.add_zero] at h
  rw [equiv_is_myequal, myequal, zerox, zeroy, mynat.add_zero, mynat.add_zero]
  rw [equiv_is_myequal, myequal, zerox, zeroy, mynat.add_zero, mynat.add_zero]
  apply Or.elim (Classical.em (a.x = a.y))
  . intro h'
    apply Or.intro_left
    exact h'
  . intro h'
    apply Or.intro_right
    have h'' : a.x ≠ a.y := h'
    have hfull : a.x * b.x + a.y * b.y + a.x * b.y + a.y * b.x = a.x * b.y + a.y * b.x + a.x * b.y + a.y * b.x := by rw [h]
    cases mynat.le_total a.x a.y
    case right.h.inl hh =>
      rw [mynat.le_iff_exists_add] at hh
      cases hh with
      | intro c hc =>
        rw [hc] at hfull
        repeat rw [mynat.add_mul] at hfull
        simp at hfull
        have := mynat.add_left_cancel (c * b.x) _ _ hfull
        have := mynat.add_left_cancel _ _ _ this
        have := mynat.add_left_cancel _ _ _ this
        repeat rw [← mynat.add_assoc] at this
        rw [mynat.add_comm (c * b.x) _] at this
        have := mynat.add_right_cancel _ _ _ this
        have hlast := mynat.add_left_cancel _ _ _ this
        rename_i h_ h__ h___ -- this is so dirty ...
        cases c
        case zero =>
          apply False.elim
          rw [mynat.mynat_zero_eq_zero] at hc
          rw [mynat.add_zero] at hc
          exact h'' (Eq.symm hc)
        case succ d =>
          have hsnez := mynat.succ_ne_zero d
          exact Eq.symm (mynat.mul_left_cancel (mynat.succ d) b.y b.x hsnez hlast)
    case right.h.inr hh =>
      rw [mynat.le_iff_exists_add] at hh
      cases hh with
      | intro c hc =>
        rw [hc] at hfull
        repeat rw [mynat.add_mul] at hfull
        simp at hfull
        have := mynat.add_left_cancel _ _ _ hfull
        rw [← mynat.add_assoc (b.x * a.y) _ _] at this
        rw [mynat.add_comm (b.x * a.y) _] at this
        rw [mynat.add_assoc (a.y * b.y) _ _] at this
        have := mynat.add_right_cancel (c * b.x) (a.y * b.y + (b.x * a.y + (c * b.y + a.y * b.y))) (c * b.y) this
        rename_i h_ -- this is so dirty ...
        cases c
        case zero =>
          apply False.elim
          rw [mynat.mynat_zero_eq_zero] at hc
          rw [mynat.add_zero] at hc
          exact h'' hc
        case succ d =>
          have hsnez := mynat.succ_ne_zero d
          exact mynat.mul_left_cancel (mynat.succ d) b.x b.y hsnez this

theorem mul_eq_zero_iff (a b : myint): a * b ≈ 0 ↔ a ≈ 0 ∨ b ≈ 0 := by
  apply Iff.intro
  . intro h
    exact eq_zero_or_eq_zero_of_mul_eq_zero a b h
  . intro h
    cases h
    . rename_i hh
      have := mul_right a 0 b hh
      exact trans this (zero_mul b)
    . rename_i hh
      have := mul_right b 0 a hh
      have := trans this (zero_mul a)
      have := trans (mul_comm a b) this
      exact this

theorem mul_left_cancel (a b c : myint) (ha : a ≉ 0) : a * b ≈ a * c → b ≈ c := by
  intro h
  have := (sub_right (a * b) (a * c) (a * c)) h
  repeat rw [sub_eq_plusneg] at this
  have hez : a * b + -(a * c) ≈ 0 := trans this (neg_is_inv _)
  have : -(a * c) ≈ a * c * -1 := (symm (mul_negone (a * c)))
  have : a * b + -(a * c) ≈ a * b + a * c * -1 := add_left (a * b) _ _ this
  have : a * b + a * c * -1 ≈ 0 := trans (symm this) hez
  have hma : a * c * -1 ≈ a * (c * -1) := mul_assoc _ _ _
  have hz : a * b + a * (c * -1) ≈ 0 := trans (symm (add_left (a * b) _ _ hma)) this
  have := mul_add a b (c * -1)
  have : a * (b + c * -1) ≈ 0 := trans this hz
  have heitherzero := eq_zero_or_eq_zero_of_mul_eq_zero a (b + c * -1) this
  cases heitherzero
  case inl haz =>
    apply False.elim
    exact ha haz
  case inr hs =>
    have : c + (b + c * -1) ≈ c + 0 := add_left c (b + c * -1) 0 hs
    have hbc : c + b + c * -1 ≈ c + 0 := trans (add_assoc _ _ _) this
    have : c * -1 ≈ -c := mul_negone c
    have : c + b + c * -1 ≈ c + b + -c := add_left _ _ _ this
    have : c + b + -c ≈ c + 0 := trans (symm this) hbc
    have hlast : c + b + -c ≈ c := trans this (add_zero c)
    have hcomm := add_comm b c
    have := add_right (b + c) (c + b) (-c) hcomm
    have : b + c + -c ≈ c := trans this hlast
    have hg : b + (c + -c) ≈ c := trans (symm (add_assoc _ _ _)) this
    have : b + (c + -c) ≈ b + 0 := (add_left b _ _) (neg_is_inv c)
    exact trans (symm this) hg

end myint