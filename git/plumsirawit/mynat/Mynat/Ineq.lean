import Mynat.MulAdv

namespace mynat

def myle (a b : mynat) :=  ∃ (c : mynat), b = a + c
instance : LE mynat where
  le := myle
theorem le_iff_exists_add (a b : mynat) : a ≤ b ↔ ∃ (c : mynat), b = a + c := Iff.rfl

theorem one_add_le_self (x : mynat) : x ≤ 1 + x := by
  rw [le_iff_exists_add]
  exists 1
  rw [add_comm]

theorem le_refl (x : mynat) : x ≤ x :=
  Exists.intro 0 rfl

-- attribute [rfl] mynat.le_refl
-- Why doesn't it work?

theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) := by
  intro h
  cases h with
  | intro c hc =>
    exists succ c
    rw [add_succ]
    rw [hc]

theorem zero_le (a : mynat) : 0 ≤ a := by
  rw [le_iff_exists_add]
  exists a
  rw [zero_add]

theorem le_trans (a b c : mynat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [le_iff_exists_add] at hab hbc
  cases hab with
  | intro d hd =>
    cases hbc with
    | intro e he =>
      rw [hd] at he
      exists d + e
      rw [← add_assoc]
      exact he

theorem le_antisymm (a b : mynat) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with
  | intro c hc =>
    cases hba with
    | intro d hd =>
      rw [hc] at hd
      conv at hd =>
        lhs
        rw [← add_zero a]
      rw [add_assoc] at hd
      have halc := (add_left_cancel a 0 (c+d)) hd
      have halcsym := Eq.symm halc
      have hcez := add_right_eq_zero halcsym
      rw [hcez] at hc
      rw [add_zero] at hc
      exact Eq.symm hc

theorem le_zero (a : mynat) (h : a ≤ 0) : a = 0 := by
  have hh := zero_le a
  exact le_antisymm a 0 h hh

theorem succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b := by
  cases h with
  | intro c hc =>
    exists c
    rw [hc]
    rw [succ_add]

theorem le_total (a b : mynat) : a ≤ b ∨ b ≤ a := by
  cases b
  case zero =>
    apply Or.intro_right
    exact zero_le a
  case succ b' =>
    have hind := le_total a b'
    cases hind
    case inl h =>
      apply Or.intro_left
      cases h with
      | intro c hc =>
        exists succ c
        rw [add_succ]
        rw [hc]
    case inr h =>
      cases h with
      | intro c hc =>
        cases c
        case zero =>
          rw [mynat_zero_eq_zero] at hc
          apply Or.intro_left
          exists 1
          rw [hc]
          rw [add_assoc]
          rw [zero_add]
          exact succ_eq_add_one b'
        case succ c' =>
          apply Or.intro_right
          exists c'
          rw [hc]
          rw [succ_add]
          rw [add_succ]

theorem le_succ_self (a : mynat) : a ≤ succ a := by
  exists 1

theorem add_le_add_right {a b : mynat} : a ≤ b → ∀ t, (a + t) ≤ (b + t) := by
  intro h
  cases h with
  | intro c hc =>
    intro t
    exists c
    rw [hc]
    rw [add_assoc]
    rw [add_assoc]
    rw [add_comm c t]

theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b := by
  intro h
  cases h with
  | intro c hc =>
    exists c
    rw [succ_eq_add_one] at hc
    rw [succ_eq_add_one] at hc
    rw [add_comm b 1] at hc
    rw [add_comm a 1] at hc
    rw [add_assoc] at hc
    exact add_left_cancel 1 b (a + c) hc

theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) := by
  intro h
  cases h with
  | intro c hc =>
    rw [succ_eq_add_one] at hc
    conv at hc =>
      lhs
      rw [← add_zero a]
    rw [add_assoc] at hc
    have hd := add_left_cancel a 0 (1 + c) hc
    rw [add_comm] at hd
    rw [← succ_eq_add_one] at hd
    have hnd := zero_ne_succ c
    exact hnd hd

theorem add_le_add_left {a b : mynat} (h : a ≤ b) (t : mynat) :
  t + a ≤ t + b := by
  cases h with
  | intro c hc =>
    exists c
    rw [hc]
    rw [← add_assoc]

theorem lt_aux_one (a b : mynat) : a ≤ b ∧ ¬ (b ≤ a) → succ a ≤ b := by
  intro h
  have h1 := h.left
  have h2 := h.right
  cases h1 with
  | intro c hc =>
    cases c
    case zero =>
      rw [mynat_zero_eq_zero] at hc
      -- by contradiction
      rw [add_zero] at hc
      rw [hc] at h2
      apply False.elim
      exact h2 (le_refl a)
    case succ c' =>
      exists c'
      rw [succ_add]
      rw [add_succ] at hc
      exact hc

theorem lt_aux_two (a b : mynat) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) := by
  intro h
  cases h with
  | intro c hc =>
    apply And.intro
    case intro.left =>
      exists succ c
      rw [add_succ]
      rw [succ_add] at hc
      exact hc
    case intro.right =>
      intro hh
      rw [hc] at hh
      rw [succ_add] at hh
      rw [← add_succ] at hh
      cases hh with
      | intro d hd =>
        conv at hd =>
          lhs
          rw [← add_zero a]
        rw [add_assoc] at hd
        have hfalse := add_left_cancel a 0 (succ c + d) hd
        have hsz := add_right_eq_zero (Eq.symm hfalse)
        exact zero_ne_succ c (Eq.symm hsz)

def mylt (a b : mynat) := a ≤ b ∧ ¬ (b ≤ a)
-- incantation so that we can use `<` notation: 
instance : LT mynat := ⟨mylt⟩
theorem lt_def (a b : mynat) : a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := Iff.rfl

theorem lt_iff_succ_le (a b : mynat) : a < b ↔ succ a ≤ b := by
  rw [lt_def]
  apply Iff.intro
  . apply lt_aux_one
  . apply lt_aux_two

end mynat