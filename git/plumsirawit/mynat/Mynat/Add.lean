import Mynat.Base

namespace mynat

def myadd (m n : mynat) : mynat :=
  match n with
  | 0   => m
  | succ n' => succ (myadd m n')

instance : Add mynat where
  add := myadd

theorem add_zero (m : mynat) : m + 0 = m := rfl
theorem add_succ (m n : mynat) : m + succ n = succ (m + n) := rfl

theorem zero_add (n : mynat) : 0 + n = n := by
  cases n
  . rfl
  case succ m =>
    have h := congrArg succ (zero_add m)
    rw [←add_succ] at h
    exact h

theorem add_assoc (a b c : mynat) : (a + b) + c = a + (b + c) := by
  cases c
  case zero =>
    rw [mynat_zero_eq_zero]
    repeat {rw [add_zero]}
    rfl
  case succ m =>
    rw [add_succ]
    rw [add_succ]
    rw [add_succ]
    rw [add_assoc a b m]

theorem succ_add (a b : mynat) : succ a + b = succ (a + b) := by
  cases b
  case zero =>
    rw [mynat_zero_eq_zero]
    repeat {rw [add_zero]}
    rfl
  case succ m =>
    rw [add_succ]
    rw [add_succ]
    rw [succ_add a m]

theorem add_comm (a b : mynat) : a + b = b + a := by
  cases b
  case zero =>
    rw [mynat_zero_eq_zero]
    rw [add_zero]
    rw [zero_add]
  case succ m =>
    rw [add_succ]
    rw [succ_add]
    rw [add_comm a m]

theorem succ_eq_add_one (n : mynat) : succ n = n + 1 := by
  rw [one_eq_succ_zero]
  rw [add_succ n 0]
  rw [add_zero]

theorem add_right_comm (a b c : mynat) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_assoc]
  rw [add_comm b c]

attribute [simp] add_assoc add_comm add_right_comm

end mynat