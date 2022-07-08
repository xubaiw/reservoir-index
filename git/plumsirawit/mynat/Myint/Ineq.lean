import Myint.Canon

namespace myint

theorem ne_irrefl (a : myint) : ¬ a ≉ a := by
  rw [mynotequal]
  rw [Ne]
  have := refl a
  rw [myequal] at this
  rw [this]
  have : ¬ a.y + a.x = a.y + a.x → False := by
    intro h
    rw [← Ne] at h
    exact Ne.irrefl h
  exact this

theorem ne_symm {a b : myint} (hab : mynotequal a b) : mynotequal b a := by
  rw [mynotequal] at hab ⊢
  have hres := Ne.symm hab
  rw [mynat.add_comm a.y, mynat.add_comm a.x] at hres
  exact hres

-- Warning: this is not the usual transitivity.
-- this says that if a ≠ b and b = c then a ≠ c
theorem ne_trans {a b c : myint} (hab : mynotequal a b) (hbc : myequal b c) : mynotequal a c := by
  rw [myequal] at hbc
  rw [mynotequal] at hab ⊢
  have : a.x + b.y + (b.x + c.y) ≠ a.y + b.x + (b.y + c.x) := by
    rw [hbc]
    intro h
    have := mynat.add_right_cancel (a.x + b.y) (b.y + c.x) (a.y + b.x) h
    exact hab this
  repeat rw [← mynat.add_assoc] at this
  rw [mynat.add_assoc a.x] at this
  rw [mynat.add_comm b.y] at this
  rw [mynat.add_comm a.x] at this
  rw [mynat.add_assoc a.y] at this
  rw [mynat.add_comm a.y] at this
  repeat rw [mynat.add_assoc (b.x + b.y)] at this
  intro hfalse
  rw [hfalse] at this
  exact this (Eq.refl (b.x + b.y + (a.y + c.x)))


theorem ne_implies_exists_offset (a b : myint) : a ≉ b → ∃ c : myint, c ≉ 0 ∧ a ≈ b + c := by
  intro h
  rw [mynotequal] at h
  cases mynat.le_total (a.x + b.y) (a.y + b.x)
  case inl hle =>
    rw [mynat.le_iff_exists_add] at hle
    cases hle with
    | intro d hd =>
      exists myint.mk 0 d
      apply And.intro
      . rw [mynotequal]
        rw [destruct_x, destruct_y _ d]
        rw [default_nat_has_no_y, default_nat_has_same_x]
        rw [mynat.myofnat, mynat.mynat_zero_eq_zero]
        repeat rw [mynat.add_zero]
        cases d
        case zero =>
          apply False.elim _
          rw [mynat.mynat_zero_eq_zero, mynat.add_zero] at hd
          exact h (Eq.symm hd)
        case succ d' =>
          exact Ne.symm (mynat.succ_ne_zero d')
      . rw [equiv_is_myequal, myequal]
        rw [add_y, destruct_y _ d]
        rw [add_x, destruct_x 0 _]
        rw [mynat.add_zero]
        rw [← mynat.add_assoc]
        exact Eq.symm hd
  case inr hle =>
    rw [mynat.le_iff_exists_add] at hle
    cases hle with
    | intro d hd =>
      exists myint.mk d 0
      apply And.intro
      . rw [mynotequal]
        rw [destruct_x, destruct_y _ 0]
        rw [default_nat_has_no_y, default_nat_has_same_x]
        rw [mynat.myofnat, mynat.mynat_zero_eq_zero]
        repeat rw [mynat.zero_add]
        cases d
        case zero =>
          apply False.elim _
          rw [mynat.mynat_zero_eq_zero, mynat.add_zero] at hd
          exact h hd
        case succ d' =>
          rw [mynat.add_zero]
          exact mynat.succ_ne_zero d'
      . rw [equiv_is_myequal, myequal]
        rw [add_y, destruct_y _ 0]
        rw [add_x, destruct_x d _]
        rw [mynat.add_zero]
        rw [← mynat.add_assoc]
        exact hd

theorem ne_iff_exists_offset (a b : myint) : a ≉ b ↔ ∃ c : myint, c ≉ 0 ∧ a ≈ b + c := by
  apply Iff.intro
  . exact ne_implies_exists_offset a b
  . intro h
    cases h with
    | intro d hd =>
      have hdnz := hd.left
      have hab := hd.right
      rw [mynotequal]
      rw [equiv_is_myequal, myequal] at hab
      rw [add_y, add_x] at hab
      rw [mynotequal, zerox, zeroy, mynat.add_zero, mynat.add_zero] at hdnz
      intro hcont
      repeat rw [← mynat.add_assoc] at hab
      rw [hcont] at hab
      have := (mynat.add_left_cancel _ _ _) hab
      exact hdnz (Eq.symm this)

theorem ne_mul_still_ne (a b t : myint) : a ≉ b ∧ t ≉ 0 → a * t ≉ b * t := by
  intro h
  have hab := h.left
  have htnz := h.right
  have hoffset := (ne_iff_exists_offset a b).mp hab
  cases hoffset with
  | intro c hc =>
    have hcnz := hc.left
    have habc := hc.right
    have htimes := mul_right a (b + c) t habc
    have : a * t ≈ b * t + c * t := trans htimes (add_mul b c t)
    intro hfalse
    rw [← myequal, ← equiv_is_myequal] at hfalse
    have := trans (symm hfalse) this
    have := add_left_cancel (b * t) 0 (c * t) this
    have := eq_zero_or_eq_zero_of_mul_eq_zero c t (symm this)
    cases this
    case inl h' =>
      exact hcnz h'
    case inr h' =>
      exact htnz h'

theorem mul_nonzero (a b : myint) : a ≉ 0 → b ≉ 0 → a * b ≉ 0 := by
  intro ha
  intro hb
  have := ne_mul_still_ne a 0 b ⟨ ha, hb ⟩
  have := ne_trans this (zero_mul b)
  exact this

def myle (a b : myint) :=  ∃ (c : mynat), b ≈ a + (myint.mk c 0)
instance : LE myint where
  le := myle
theorem le_iff_exists_add (a b : myint) : a ≤ b ↔ ∃ (c : mynat), b ≈ a + (myint.mk c 0) := Iff.rfl

theorem le_refl (x : myint) : x ≤ x := by
  exists 0
  exact add_zero x

theorem le_refl_equiv (x y : myint) : x ≈ y → x ≤ y := by
  intro h
  exists 0
  exact trans (symm h) (add_zero x)

theorem le_trans (a b c : myint) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases hab with
  | intro d hd =>
    cases hbc with
    | intro e he =>
      have hdp := add_right b (a + myint.mk d 0) (myint.mk e 0) hd
      have heq : c ≈ (a + (myint.mk d 0) + (myint.mk e 0)) := trans he hdp
      exists d + e
      have heqasc : c ≈ a + ((myint.mk d 0) + (myint.mk e 0)) := trans heq (add_assoc a (myint.mk d 0) (myint.mk e 0))
      conv at heqasc =>
        rhs
        arg 2
        rw [add_eq_myadd, myadd]
        rw [destruct_x, destruct_y, destruct_x, mynat.add_zero]
      exact heqasc

theorem le_trans_equiv (a b c : myint) (hab : a ≤ b) (hbc : b ≈ c) : a ≤ c := by
  have := le_refl_equiv b c hbc
  exact le_trans a b c hab this

theorem le_equiv_trans (a b c : myint) (hab : a ≈ b) (hbc : b ≤ c) : a ≤ c := by
  have := le_refl_equiv a b hab
  exact le_trans a b c this hbc

theorem le_antisymm (a b : myint) (hab : a ≤ b) (hba : b ≤ a) : a ≈ b := by
  cases hab with
  | intro c hc =>
    cases hba with
    | intro d hd =>
      have hadd : b + (myint.mk d 0) ≈ a + (myint.mk c 0) + (myint.mk d 0) := add_right _ _ _ hc
      have hassoc : b + (myint.mk d 0) ≈ a + ((myint.mk c 0) + (myint.mk d 0)) := trans hadd (add_assoc _ _ _)
      have := trans hd hassoc
      have := add_left_cancel a 0 _ this
      rw [equiv_is_myequal, myequal] at this
      rw [add_x, destruct_x c _, destruct_x d _, zerox] at this
      rw [add_y, destruct_y, zeroy] at this
      repeat rw [mynat.zero_add] at this
      have hdz := mynat.add_left_eq_zero (Eq.symm this)
      rw [hdz] at hd
      have hzz : myint.mk 0 0 ≈ 0 := rfl
      have := trans hd (add_left b _ _ hzz)
      have := trans this (add_zero b)
      exact this

theorem add_le_add_right {a b : myint} : a ≤ b → ∀ t, (a + t) ≤ (b + t) := by
  intro h
  rw [le_iff_exists_add] at h
  cases h with
  | intro c hc =>
    intro t
    exists c
    have ht1 := add_right b (a + myint.mk c 0) t hc
    have ht2 : a + { x := c, y := 0 } + t ≈ a + t + { x := c, y := 0} := by
      have hst1 : a + (myint.mk c 0) + t ≈ a + ((myint.mk c 0) + t) := add_assoc _ _ _
      have hst2 : a + ((myint.mk c 0) + t) ≈ a + (t + (myint.mk c 0)) := add_left a _ _ (add_comm _ _)
      have hst3 : a + (t + (myint.mk c 0)) ≈ a + t + (myint.mk c 0) := symm (add_assoc _ _ _)
      exact trans (trans hst1 hst2) hst3
    exact trans ht1 ht2

theorem le_total (a b : myint) : a ≤ b ∨ b ≤ a := by
  have hlemma (n : myint) : n ≤ 0 ∨ 0 ≤ n := by
    let pn := n.x ≤ n.y
    cases Classical.em pn
    case inl h =>
      have : n.x ≤ n.y := h
      apply Or.intro_left
      rw [le_iff_exists_add]
      have := canon_neg n this
      cases this with
      | intro c hc =>
        exists c.y
        have ht1 : c + (myint.mk c.y 0) ≈ n + (myint.mk c.y 0) := add_right c n _ hc.right
        have : myint.mk 0 c.y ≈ c := by
          apply if_x_and_y_equal_then_equiv
          rw [destruct_x, destruct_y]
          exact ⟨ Eq.symm hc.left, rfl ⟩
        have ht2 : (myint.mk 0 c.y) + (myint.mk c.y 0) ≈ c + (myint.mk c.y 0) := add_right (myint.mk 0 c.y) c (myint.mk c.y 0) this
        have ht3 : 0 ≈ (myint.mk 0 c.y) + (myint.mk c.y 0) := by
          rw [equiv_is_myequal, myequal]
          rw [add_y, destruct_y, destruct_y _ 0]
          rw [add_x, destruct_x 0, destruct_x c.y]
          rw [zerox, zeroy, mynat.zero_add, mynat.add_zero, mynat.zero_add, mynat.zero_add]
        exact trans (trans ht3 ht2) ht1
    case inr h =>
      have : ¬ n.x ≤ n.y := h
      have := mynat.le_total n.x n.y
      cases this
      case inl hh =>
        apply False.elim
        exact this hh
      case inr hh =>
        apply Or.intro_right
        rw [le_iff_exists_add]
        have := canon_pos n hh
        cases this with
        | intro c hc =>
          have ⟨ cx, cy ⟩ := c
          exists cx
          have : cy = 0 := hc.left
          rw [← this]
          exact trans (symm hc.right) (symm (zero_add (myint.mk cx cy)))
  have : a - b ≤ 0 ∨ 0 ≤ a - b := hlemma (a - b)
  have hmain : a ≈ a - b + b := by
    have hm := add_left a 0 (-b + b) (symm (trans (add_comm (-b) b) (neg_is_inv b)))
    have := equal_implies_equiv _ _ (Eq.symm (sub_eq_plusneg a b))
    have := add_right (a + -b) (a - b) b this
    have hl := symm (add_zero a)
    have hr : a + (-b + b) ≈ a + -b + b := symm (add_assoc a (-b) b)
    exact trans (trans hl hm) hr
  have haux : 0 + b ≈ b := zero_add b
  cases this
  case inl h =>
    have : (a - b) + b ≤ 0 + b := add_le_add_right h b
    apply Or.intro_left
    exact le_trans_equiv _ _ _ (le_equiv_trans _ _ _ hmain this) haux
  case inr h =>
    have : 0 + b ≤ (a - b) + b := add_le_add_right h b
    apply Or.intro_right
    exact le_trans_equiv _ _ _ (le_equiv_trans _ _ _ (symm haux) this) (symm hmain)

  -- This law is called "material implication" and I'm not sure if there is a better way to maintain this law?
  -- have : (¬ a ≤ b → b ≤ a) → a ≤ b ∨ b ≤ a := by
  --   intro h1
  --   let p : Prop := a ≤ b
  --   cases (Classical.em p)
  --   case inl hp =>
  --     apply Or.intro_left
  --     have h : a ≤ b := hp
  --     exact h
  --   case inr hnotp =>
  --     apply Or.intro_right
  --     have h : ¬ a ≤ b := hnotp
  --     exact h1 h
  -- apply this
  -- intro h
  -- rw [LE.le, instLEMyint] at h
  -- simp at h
  -- rw [myle] at h
  -- -- Another logic law
  -- sorry

theorem add_le_add_left {a b : myint} (h : a ≤ b) (t : myint) : t + a ≤ t + b := by
  have := add_le_add_right h t
  exact le_trans_equiv _ _ _ (le_equiv_trans _ _ _ (add_comm t a) this) (add_comm b t)

theorem pos_iff_y_le_x (n : myint) : 0 ≤ n ↔ n.y ≤ n.x := by
  apply Iff.intro
  . intro h
    rw [le_iff_exists_add] at h
    cases h with
    | intro c hc =>
      have ⟨ nx, ny ⟩ := n
      rw [equiv_is_myequal, myequal] at hc
      rw [destruct_x, destruct_y _ ny] at hc
      rw [add_y, add_x] at hc
      rw [destruct_y _ 0, destruct_x c _] at hc
      rw [destruct_y, destruct_x]
      exists c
      rw [zeroy, zerox, mynat.add_zero, mynat.zero_add, mynat.add_zero] at hc
      exact hc
  . intro h
    have := canon_pos n h
    cases this with
    | intro c hc =>
      have ⟨ cx, cy ⟩ := c
      rw [destruct_y] at hc
      have ⟨ hc1, hc2 ⟩ := hc
      rw [hc1] at hc2
      have : 0 ≤ myint.mk cx 0 := by
        exists cx
        exact symm (zero_add (myint.mk cx 0))
      exact le_trans_equiv _ _ _ this hc2

theorem le_mul_pos (a b : myint) (h : a ≤ b) (t : myint) (ht : 0 ≤ t) : a * t ≤ b * t := by
  have hpos := ht
  rw [le_iff_exists_add] at hpos
  cases h with
  | intro c hc =>
    have := mul_right b (a + myint.mk c 0) t hc
    have huse : b * t ≈ a * t + (myint.mk c 0) * t := trans this (add_mul _ _ _)
    have := canon_pos t ((pos_iff_y_le_x t).mp ht)
    cases this with
    | intro d hd =>
      have ⟨ dx, dy ⟩ := d
      rw [destruct_y] at hd
      have ⟨ hd1, hd2 ⟩ := hd
      rw [hd1] at hd2
      have hhelper : a * t + { x := c, y := 0 } * t ≈ a * t + { x := c, y := 0 } * { x := dx, y := 0} := (add_left (a * t) _ _) (mul_left (myint.mk c 0) t (myint.mk dx 0) (symm hd2))
      have hthis := trans huse hhelper
      conv at hthis =>
        rhs
        arg 2
        rw [mul_eq_mymul, mymul]
        rw [destruct_x, destruct_x, destruct_y]
        rw [mynat.mul_zero, mynat.mul_zero, mynat.zero_mul, mynat.add_zero, mynat.add_zero]
      exists c * dx

theorem le_mul_neg (a b : myint) (h : a ≤ b) (t : myint) (ht : t ≤ 0) : b * t ≤ a * t := by
  have : a * (-t) ≤ b * (-t) := by
    have : 0 ≤ -t := by
      have := add_le_add_right ht (-t)
      have := le_equiv_trans _ _ _ (symm (neg_is_inv t)) this
      exact le_trans_equiv _ _ _ this (zero_add _)
    exact le_mul_pos a b h (-t) this
  have hlemma (f g : myint) : f * g + f * -g ≈ 0 := by
    have : f * g + f * g * -1 ≈ f * g + f * -g := add_left _ _ _ (trans (mul_assoc _ _ _) (mul_left f _ _ (mul_negone g)))
    have hs3 : f * g * -1 ≈ - (f * g) := mul_negone (f * g)
    have hs : f * g + -(f * g) ≈ f * g + f * -g := trans (symm (add_left (f * g) _ _ hs3)) this
    have ht := trans (symm (neg_is_inv (f * g))) hs
    exact symm ht
  have : 0 ≤ a * t + b * (-t) := by
    have hthis := add_le_add_left this (a * t)
    exact le_equiv_trans _ _ _ (symm (hlemma a t)) hthis
  have hthis := add_le_add_right this (b * t)
  have := le_trans_equiv _ _ _ hthis (add_assoc _ _ _)
  have hadjust := add_left (a * t) _ _ (trans (add_comm _ _) (hlemma b t))
  have := le_trans_equiv _ _ _ this hadjust
  exact le_equiv_trans _ _ _ (symm (zero_add (b * t))) this

theorem sq_pos (n : myint) : 0 ≤ n * n := by
  let pn := 0 ≤ n
  cases Classical.em pn
  case inl h =>
    have : 0 ≤ n := h
    have := le_mul_pos 0 n this n this
    exact le_equiv_trans _ _ _ (symm (zero_mul n)) this
  case inr h =>
    have : ¬ 0 ≤ n := h
    have := le_total 0 n
    cases this
    case inl hh =>
      apply False.elim
      exact this hh
    case inr hh =>
      have := le_mul_neg n 0 hh n hh
      exact le_equiv_trans _ _ _ (symm (zero_mul n)) this

-- actually this obviously implies the simple case of AM-GM inequality...

def mylt (a b : mynat) := a ≤ b ∧ ¬ (b ≤ a)
instance : LT mynat := ⟨mylt⟩
theorem lt_def (a b : mynat) : a < b ↔ a ≤ b ∧ ¬ (b ≤ a) := Iff.rfl

end myint