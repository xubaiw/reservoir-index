import Mynat.AddAdv
import Mynat.Mul

namespace mynat

theorem mul_pos (a b : mynat) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  intro h1
  intro h2
  cases a
  case zero =>
    rw [mynat_zero_eq_zero]
    rw [zero_mul]
    exact h1
  case succ a' =>
    cases b
    case zero =>
      rw [mynat_zero_eq_zero]
      rw [mul_zero]
      exact h2
    case succ b' =>
      rw [mul_succ]
      rw [succ_mul]
      rw [add_succ]
      exact succ_ne_zero _

theorem eq_zero_or_eq_zero_of_mul_eq_zero (a b : mynat) (h : a * b = 0) :
  a = 0 ∨ b = 0 := by
  cases a
  case zero =>
    rw [mynat_zero_eq_zero]
    apply Or.intro_left
    rfl
  case succ a' =>
    cases b
    case zero =>
      rw [mynat_zero_eq_zero]
      apply Or.intro_right
      rfl
    case succ b' =>
      apply False.elim
      have samtz := succ_ne_zero a'
      have sbmtz := succ_ne_zero b'
      have hfalse := (mul_pos (succ a') (succ b')) samtz sbmtz
      exact hfalse h

theorem mul_eq_zero_iff (a b : mynat): a * b = 0 ↔ a = 0 ∨ b = 0 := by
  apply Iff.intro
  . intro H
    exact eq_zero_or_eq_zero_of_mul_eq_zero a b H
  . intro h
    apply Or.elim h
    . intro hz
      rw [hz]
      rw [zero_mul]
    . intro hz
      rw [hz]
      rw [mul_zero]

theorem mul_left_cancel (a b c : mynat) (ha : a ≠ 0) : a * b = a * c → b = c := by
  induction c generalizing b
  case zero =>
    rw [mynat_zero_eq_zero]
    rw [mul_zero]
    intro h
    have aorb := (mul_eq_zero_iff a b).mp h
    cases aorb
    case inl hh =>
      apply False.elim
      exact ha hh
    case inr hh =>
      exact hh
  case succ c' hc =>
    rw [mul_succ]
    cases b
    case zero =>
      rw [mynat_zero_eq_zero]
      rw [mul_zero]
      intro h'
      have h'' := (calc
        a * c' + a = 0 := by rw[h']
      )
      have haz := add_left_eq_zero h''
      apply False.elim
      exact ha haz
    case succ b' =>
      rw [mul_succ]
      intro hhh
      have bec := (add_right_cancel (a * b') a (a * c')) hhh
      rw [succ_eq_succ_iff b' c']
      exact hc b' bec


end mynat