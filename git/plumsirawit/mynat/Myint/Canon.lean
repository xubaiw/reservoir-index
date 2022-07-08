import Myint.Mul

namespace myint

-- Optional: Canonical representation of the integers
-- Satisfied by n ≈ (n'.x, n'.y) where n'.x = 0 or n'.y = 0

theorem arbitrary_representation : ∀ k : mynat, k ≤ n.x ∧ k ≤ n.y → ∃ m : myint, (m.x + k = n.x ∧ m.y + k = n.y) ∧ m ≈ n := by
  intro z
  induction z
  case zero =>
    rw [mynat.mynat_zero_eq_zero]
    intro _
    exists n
    repeat rw [mynat.add_zero]
    apply And.intro
    . apply And.intro
      . rfl
      . rfl
    . exact refl n
  case succ z' hz =>
    intro hgoal
    have := mynat.le_succ _ _ hgoal.left
    have hl := mynat.le_of_succ_le_succ _ _ this
    have := mynat.le_succ _ _ hgoal.right
    have hr := mynat.le_of_succ_le_succ _ _ this
    have hind := hz ⟨ hl, hr ⟩
    cases hind with
    | intro d hd =>
      have ⟨ dx, dy ⟩ := d
      cases dx
      case zero =>
        rw [mynat.mynat_zero_eq_zero] at hd
        rw [destruct_x, destruct_y] at hd
        have hd1 := hd.left
        have hd2 := hd.right
        rw [equiv_is_myequal, myequal] at hd2
        rw [destruct_x, destruct_y _ dy, mynat.zero_add] at hd2
        rw [mynat.zero_add] at hd1
        rw [hd2] at hd1
        have hdconc : z' = n.x := hd1.left
        apply False.elim
        have hfalse := hgoal.left
        rw [hdconc] at hfalse
        exact mynat.not_succ_le_self n.x hfalse
      case succ dx' =>
        cases dy
        case zero =>
          rw [mynat.mynat_zero_eq_zero] at hd
          rw [destruct_x, destruct_y] at hd
          have hd1 := hd.left
          have hd2 := hd.right
          rw [equiv_is_myequal, myequal] at hd2
          rw [destruct_x, destruct_y, destruct_y _ 0, mynat.zero_add] at hd2
          rw [mynat.zero_add] at hd1
          have hdconc : z' = n.y := hd1.right
          apply False.elim
          have hfalse := hgoal.right
          rw [hdconc] at hfalse
          exact mynat.not_succ_le_self n.y hfalse
        case succ dy' =>
          rw [destruct_x, destruct_y] at hd
          have hd1 := hd.left
          have hd2 := hd.right
          rw [equiv_is_myequal, myequal] at hd2
          rw [destruct_x, destruct_y _ (mynat.succ dy')] at hd2
          rw [mynat.succ_add, mynat.succ_add] at hd2
          have hd2conc := mynat.succ_inj hd2
          exists myint.mk dx' dy'
          rw [destruct_x, destruct_y]
          rw [mynat.add_succ, ← mynat.succ_add, mynat.add_succ, ← mynat.succ_add]
          rw [equiv_is_myequal, myequal, destruct_x dx' _, destruct_y _ dy']
          exact ⟨ hd1, hd2conc ⟩

theorem canon_neg (n : myint) : n.x ≤ n.y → ∃ n' : myint, n'.x = 0 ∧ n' ≈ n := by
  intro h
  have := arbitrary_representation n.x ⟨ mynat.le_refl n.x, h ⟩ 
  cases this with
  | intro c hc =>
    have hc1 := hc.left.left
    have hc3 := hc.right
    exists c
    apply And.intro
    . rw [mynat.add_comm] at hc1
      exact mynat.eq_zero_of_add_right_eq_self hc1
    . exact hc3

theorem canon_pos (n : myint) : n.y ≤ n.x → ∃ n' : myint, n'.y = 0 ∧ n' ≈ n := by
  intro h
  have := arbitrary_representation n.y ⟨ h, mynat.le_refl n.y ⟩
  cases this with
  | intro c hc =>
    have hc2 := hc.left.right
    have hc3 := hc.right
    exists c
    apply And.intro
    . rw [mynat.add_comm] at hc2
      exact mynat.eq_zero_of_add_right_eq_self hc2
    . exact hc3

theorem canon (n : myint) : ∃ n' : myint, (n'.x = 0 ∨ n'.y = 0) ∧ n' ≈ n := by
  let pn := n.x ≤ n.y
  cases Classical.em pn
  case inl h =>
    have : n.x ≤ n.y := h
    have := canon_neg n this
    cases this with
    | intro c hc =>
      exists c
      apply And.intro
      . apply Or.intro_left
        exact hc.left
      . exact hc.right
  case inr h =>
    have hf : ¬n.x ≤ n.y := h
    have : n.x ≤ n.y ∨ n.y ≤ n.x := mynat.le_total n.x n.y
    cases this
    case inl hh =>
      apply False.elim
      exact hf hh
    case inr hh =>
      have := arbitrary_representation n.y ⟨ hh, mynat.le_refl n.y ⟩
      cases this with
      | intro c hc =>
        have hc2 := hc.left.right
        have hc3 := hc.right
        exists c
        apply And.intro
        . apply Or.intro_right
          rw [mynat.add_comm] at hc2
          exact mynat.eq_zero_of_add_right_eq_self hc2
        . exact hc3

end myint