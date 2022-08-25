/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa,
Yuyang Zhao
-/
import Mathbin.Algebra.CovariantAndContravariant
import Mathbin.Order.Monotone

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

## Remark

Almost no monoid is actually present in this file: most assumptions have been generalized to
`has_mul` or `mul_one_class`.

-/


-- TODO: If possible, uniformize lemma names, taking special care of `'`,
-- after the `ordered`-refactor is done.
open Function

variable {α β : Type _}

section Mul

variable [Mul α]

section LE

variable [LE α]

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_left]
theorem mul_le_mul_left' [CovariantClass α α (· * ·) (· ≤ ·)] {b c : α} (bc : b ≤ c) (a : α) : a * b ≤ a * c :=
  CovariantClass.elim _ bc

@[to_additive le_of_add_le_add_left]
theorem le_of_mul_le_mul_left' [ContravariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (bc : a * b ≤ a * c) : b ≤ c :=
  ContravariantClass.elim _ bc

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_right]
theorem mul_le_mul_right' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {b c : α} (bc : b ≤ c) (a : α) : b * a ≤ c * a :=
  CovariantClass.elim a bc

@[to_additive le_of_add_le_add_right]
theorem le_of_mul_le_mul_right' [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (bc : b * a ≤ c * a) :
    b ≤ c :=
  ContravariantClass.elim a bc

@[simp, to_additive]
theorem mul_le_mul_iff_left [CovariantClass α α (· * ·) (· ≤ ·)] [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α)
    {b c : α} : a * b ≤ a * c ↔ b ≤ c :=
  rel_iff_cov α α (· * ·) (· ≤ ·) a

@[simp, to_additive]
theorem mul_le_mul_iff_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] [ContravariantClass α α (swap (· * ·)) (· ≤ ·)]
    (a : α) {b c : α} : b * a ≤ c * a ↔ b ≤ c :=
  rel_iff_cov α α (swap (· * ·)) (· ≤ ·) a

end LE

section LT

variable [LT α]

@[simp, to_additive]
theorem mul_lt_mul_iff_left [CovariantClass α α (· * ·) (· < ·)] [ContravariantClass α α (· * ·) (· < ·)] (a : α)
    {b c : α} : a * b < a * c ↔ b < c :=
  rel_iff_cov α α (· * ·) (· < ·) a

@[simp, to_additive]
theorem mul_lt_mul_iff_right [CovariantClass α α (swap (· * ·)) (· < ·)] [ContravariantClass α α (swap (· * ·)) (· < ·)]
    (a : α) {b c : α} : b * a < c * a ↔ b < c :=
  rel_iff_cov α α (swap (· * ·)) (· < ·) a

@[to_additive add_lt_add_left]
theorem mul_lt_mul_left' [CovariantClass α α (· * ·) (· < ·)] {b c : α} (bc : b < c) (a : α) : a * b < a * c :=
  CovariantClass.elim _ bc

@[to_additive lt_of_add_lt_add_left]
theorem lt_of_mul_lt_mul_left' [ContravariantClass α α (· * ·) (· < ·)] {a b c : α} (bc : a * b < a * c) : b < c :=
  ContravariantClass.elim _ bc

@[to_additive add_lt_add_right]
theorem mul_lt_mul_right' [CovariantClass α α (swap (· * ·)) (· < ·)] {b c : α} (bc : b < c) (a : α) : b * a < c * a :=
  CovariantClass.elim a bc

@[to_additive lt_of_add_lt_add_right]
theorem lt_of_mul_lt_mul_right' [ContravariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (bc : b * a < c * a) :
    b < c :=
  ContravariantClass.elim a bc

end LT

section Preorderₓ

variable [Preorderₓ α]

@[to_additive]
theorem mul_lt_mul_of_lt_of_lt [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
    {a b c d : α} (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  calc
    a * c < a * d := mul_lt_mul_left' h₂ a
    _ < b * d := mul_lt_mul_right' h₁ d
    

alias add_lt_add_of_lt_of_lt ← add_lt_add

@[to_additive]
theorem mul_lt_mul_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {a b c d : α} (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
  (mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)

@[to_additive]
theorem mul_lt_mul_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
    {a b c d : α} (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
  (mul_le_mul_left' h₂ _).trans_lt (mul_lt_mul_right' h₁ d)

/-- Only assumes left strict covariance. -/
@[to_additive "Only assumes left strict covariance"]
theorem Left.mul_lt_mul [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  mul_lt_mul_of_le_of_lt h₁.le h₂

/-- Only assumes right strict covariance. -/
@[to_additive "Only assumes right strict covariance"]
theorem Right.mul_lt_mul [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α}
    (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le h₁ h₂.le

@[to_additive add_le_add]
theorem mul_le_mul' [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)

@[to_additive]
theorem mul_le_mul_three [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {a b c d e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
  mul_le_mul' (mul_le_mul' h₁ h₂) h₃

@[to_additive]
theorem mul_lt_of_mul_lt_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a * b < c) (hle : d ≤ b) :
    a * d < c :=
  (mul_le_mul_left' hle a).trans_lt h

@[to_additive]
theorem mul_le_of_mul_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a * b ≤ c) (hle : d ≤ b) :
    a * d ≤ c :=
  @act_rel_of_rel_of_act_rel _ _ _ (· ≤ ·) _ ⟨fun _ _ _ => le_transₓ⟩ a _ _ _ hle h

@[to_additive]
theorem mul_lt_of_mul_lt_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h : a * b < c) (hle : d ≤ a) :
    d * b < c :=
  (mul_le_mul_right' hle b).trans_lt h

@[to_additive]
theorem mul_le_of_mul_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h : a * b ≤ c) (hle : d ≤ a) :
    d * b ≤ c :=
  (mul_le_mul_right' hle b).trans h

@[to_additive]
theorem lt_mul_of_lt_mul_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a < b * c) (hle : c ≤ d) :
    a < b * d :=
  h.trans_le (mul_le_mul_left' hle b)

@[to_additive]
theorem le_mul_of_le_mul_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c d : α} (h : a ≤ b * c) (hle : c ≤ d) :
    a ≤ b * d :=
  @rel_act_of_rel_of_rel_act _ _ _ (· ≤ ·) _ ⟨fun _ _ _ => le_transₓ⟩ b _ _ _ hle h

@[to_additive]
theorem lt_mul_of_lt_mul_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h : a < b * c) (hle : b ≤ d) :
    a < d * c :=
  h.trans_le (mul_le_mul_right' hle c)

@[to_additive]
theorem le_mul_of_le_mul_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (h : a ≤ b * c) (hle : b ≤ d) :
    a ≤ d * c :=
  h.trans (mul_le_mul_right' hle c)

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α]

@[to_additive]
theorem mul_left_cancel'' [ContravariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b = a * c) : b = c :=
  (le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.Ge)

@[to_additive]
theorem mul_right_cancel'' [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (h : a * b = c * b) : a = c :=
  le_antisymmₓ (le_of_mul_le_mul_right' h.le) (le_of_mul_le_mul_right' h.Ge)

end PartialOrderₓ

end Mul

-- using one
section MulOneClassₓ

variable [MulOneClassₓ α]

section LE

variable [LE α]

@[to_additive le_add_of_nonneg_right]
theorem le_mul_of_one_le_right' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : 1 ≤ b) : a ≤ a * b :=
  calc
    a = a * 1 := (mul_oneₓ a).symm
    _ ≤ a * b := mul_le_mul_left' h a
    

@[to_additive add_le_of_nonpos_right]
theorem mul_le_of_le_one_right' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (h : b ≤ 1) : a * b ≤ a :=
  calc
    a * b ≤ a * 1 := mul_le_mul_left' h a
    _ = a := mul_oneₓ a
    

@[to_additive le_add_of_nonneg_left]
theorem le_mul_of_one_le_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (h : 1 ≤ b) : a ≤ b * a :=
  calc
    a = 1 * a := (one_mulₓ a).symm
    _ ≤ b * a := mul_le_mul_right' h a
    

@[to_additive add_le_of_nonpos_left]
theorem mul_le_of_le_one_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (h : b ≤ 1) : b * a ≤ a :=
  calc
    b * a ≤ 1 * a := mul_le_mul_right' h a
    _ = a := one_mulₓ a
    

@[simp, to_additive le_add_iff_nonneg_right]
theorem le_mul_iff_one_le_right' [CovariantClass α α (· * ·) (· ≤ ·)] [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α)
    {b : α} : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans
    (by
      rw [mul_oneₓ])
    (mul_le_mul_iff_left a)

@[simp, to_additive le_add_iff_nonneg_left]
theorem le_mul_iff_one_le_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] (a : α) {b : α} : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans
    (by
      rw [one_mulₓ])
    (mul_le_mul_iff_right a)

@[simp, to_additive add_le_iff_nonpos_right]
theorem mul_le_iff_le_one_right' [CovariantClass α α (· * ·) (· ≤ ·)] [ContravariantClass α α (· * ·) (· ≤ ·)] (a : α)
    {b : α} : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans
    (by
      rw [mul_oneₓ])
    (mul_le_mul_iff_left a)

@[simp, to_additive add_le_iff_nonpos_left]
theorem mul_le_iff_le_one_left' [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans
    (by
      rw [one_mulₓ])
    (mul_le_mul_iff_right b)

end LE

section LT

variable [LT α]

@[to_additive lt_add_of_pos_right]
theorem lt_mul_of_one_lt_right' [CovariantClass α α (· * ·) (· < ·)] (a : α) {b : α} (h : 1 < b) : a < a * b :=
  calc
    a = a * 1 := (mul_oneₓ a).symm
    _ < a * b := mul_lt_mul_left' h a
    

@[to_additive add_lt_of_neg_right]
theorem mul_lt_of_lt_one_right' [CovariantClass α α (· * ·) (· < ·)] (a : α) {b : α} (h : b < 1) : a * b < a :=
  calc
    a * b < a * 1 := mul_lt_mul_left' h a
    _ = a := mul_oneₓ a
    

@[to_additive lt_add_of_pos_left]
theorem lt_mul_of_one_lt_left' [CovariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α} (h : 1 < b) : a < b * a :=
  calc
    a = 1 * a := (one_mulₓ a).symm
    _ < b * a := mul_lt_mul_right' h a
    

@[to_additive add_lt_of_neg_left]
theorem mul_lt_of_lt_one_left' [CovariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α} (h : b < 1) : b * a < a :=
  calc
    b * a < 1 * a := mul_lt_mul_right' h a
    _ = a := one_mulₓ a
    

@[simp, to_additive lt_add_iff_pos_right]
theorem lt_mul_iff_one_lt_right' [CovariantClass α α (· * ·) (· < ·)] [ContravariantClass α α (· * ·) (· < ·)] (a : α)
    {b : α} : a < a * b ↔ 1 < b :=
  Iff.trans
    (by
      rw [mul_oneₓ])
    (mul_lt_mul_iff_left a)

@[simp, to_additive lt_add_iff_pos_left]
theorem lt_mul_iff_one_lt_left' [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] (a : α) {b : α} : a < b * a ↔ 1 < b :=
  Iff.trans
    (by
      rw [one_mulₓ])
    (mul_lt_mul_iff_right a)

@[simp, to_additive add_lt_iff_neg_left]
theorem mul_lt_iff_lt_one_left' [CovariantClass α α (· * ·) (· < ·)] [ContravariantClass α α (· * ·) (· < ·)]
    {a b : α} : a * b < a ↔ b < 1 :=
  Iff.trans
    (by
      rw [mul_oneₓ])
    (mul_lt_mul_iff_left a)

@[simp, to_additive add_lt_iff_neg_right]
theorem mul_lt_iff_lt_one_right' [CovariantClass α α (swap (· * ·)) (· < ·)]
    [ContravariantClass α α (swap (· * ·)) (· < ·)] {a : α} (b : α) : a * b < b ↔ a < 1 :=
  Iff.trans
    (by
      rw [one_mulₓ])
    (mul_lt_mul_iff_right b)

end LT

section Preorderₓ

variable [Preorderₓ α]

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`,
which assume left covariance. -/


@[to_additive]
theorem mul_le_of_le_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b ≤ c) (ha : a ≤ 1) :
    b * a ≤ c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := mul_oneₓ b
    _ ≤ c := hbc
    

@[to_additive]
theorem mul_lt_of_le_of_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b ≤ c) (ha : a < 1) :
    b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := mul_oneₓ b
    _ ≤ c := hbc
    

@[to_additive]
theorem mul_lt_of_lt_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c) (ha : a ≤ 1) :
    b * a < c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b
    _ = b := mul_oneₓ b
    _ < c := hbc
    

@[to_additive]
theorem mul_lt_of_lt_of_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b < c) (ha : a < 1) :
    b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b
    _ = b := mul_oneₓ b
    _ < c := hbc
    

@[to_additive]
theorem mul_lt_of_lt_of_lt_one' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c) (ha : a < 1) :
    b * a < c :=
  mul_lt_of_lt_of_le_one hbc ha.le

/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_le_one`. -/
@[to_additive "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_nonpos`."]
theorem Left.mul_le_one [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
  mul_le_of_le_of_le_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one_of_le_of_lt`. -/
@[to_additive Left.add_neg_of_nonpos_of_neg
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg_of_nonpos_of_neg`."]
theorem Left.mul_lt_one_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : a ≤ 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_le_of_lt_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one_of_lt_of_le`. -/
@[to_additive Left.add_neg_of_neg_of_nonpos
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg_of_neg_of_nonpos`."]
theorem Left.mul_lt_one_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 :=
  mul_lt_of_lt_of_le_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one`. -/
@[to_additive "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg`."]
theorem Left.mul_lt_one [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
  mul_lt_of_lt_of_lt_one ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.mul_lt_one'`. -/
@[to_additive "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_neg'`."]
theorem Left.mul_lt_one' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
  mul_lt_of_lt_of_lt_one' ha hb

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`,
which assume left covariance. -/


@[to_additive]
theorem le_mul_of_le_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b ≤ c) (ha : 1 ≤ a) :
    b ≤ c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_oneₓ c).symm
    _ ≤ c * a := mul_le_mul_left' ha c
    

@[to_additive]
theorem lt_mul_of_le_of_one_lt [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b ≤ c) (ha : 1 < a) :
    b < c * a :=
  calc
    b ≤ c := hbc
    _ = c * 1 := (mul_oneₓ c).symm
    _ < c * a := mul_lt_mul_left' ha c
    

@[to_additive]
theorem lt_mul_of_lt_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c) (ha : 1 ≤ a) :
    b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_oneₓ c).symm
    _ ≤ c * a := mul_le_mul_left' ha c
    

@[to_additive]
theorem lt_mul_of_lt_of_one_lt [CovariantClass α α (· * ·) (· < ·)] {a b c : α} (hbc : b < c) (ha : 1 < a) :
    b < c * a :=
  calc
    b < c := hbc
    _ = c * 1 := (mul_oneₓ c).symm
    _ < c * a := mul_lt_mul_left' ha c
    

@[to_additive]
theorem lt_mul_of_lt_of_one_lt' [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (hbc : b < c) (ha : 1 < a) :
    b < c * a :=
  lt_mul_of_lt_of_one_le hbc ha.le

/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_le_mul`. -/
@[to_additive Left.add_nonneg "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_nonneg`."]
theorem Left.one_le_mul [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  le_mul_of_le_of_one_le ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul_of_le_of_lt`. -/
@[to_additive Left.add_pos_of_nonneg_of_pos
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos_of_nonneg_of_pos`."]
theorem Left.one_lt_mul_of_le_of_lt [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_le_of_one_lt ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul_of_lt_of_le`. -/
@[to_additive Left.add_pos_of_pos_of_nonneg
      "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos_of_pos_of_nonneg`."]
theorem Left.one_lt_mul_of_lt_of_le [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b :=
  lt_mul_of_lt_of_one_le ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul`. -/
@[to_additive Left.add_pos "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos`."]
theorem Left.one_lt_mul [CovariantClass α α (· * ·) (· < ·)] {a b : α} (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_lt_of_one_lt ha hb

/-- Assumes left covariance.
The lemma assuming right covariance is `right.one_lt_mul'`. -/
@[to_additive Left.add_pos' "Assumes left covariance.\nThe lemma assuming right covariance is `right.add_pos'`."]
theorem Left.one_lt_mul' [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α} (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_lt_of_one_lt' ha hb

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`,
which assume right covariance. -/


@[to_additive]
theorem mul_le_of_le_one_of_le [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a ≤ 1) (hbc : b ≤ c) :
    a * b ≤ c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := one_mulₓ b
    _ ≤ c := hbc
    

@[to_additive]
theorem mul_lt_of_lt_one_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : a < 1) (hbc : b ≤ c) :
    a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := one_mulₓ b
    _ ≤ c := hbc
    

@[to_additive]
theorem mul_lt_of_le_one_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a ≤ 1) (hb : b < c) :
    a * b < c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b
    _ = b := one_mulₓ b
    _ < c := hb
    

@[to_additive]
theorem mul_lt_of_lt_one_of_lt [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : a < 1) (hb : b < c) :
    a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b
    _ = b := one_mulₓ b
    _ < c := hb
    

@[to_additive]
theorem mul_lt_of_lt_one_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : a < 1) (hbc : b < c) :
    a * b < c :=
  mul_lt_of_le_one_of_lt ha.le hbc

/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_le_one`. -/
@[to_additive "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_nonpos`."]
theorem Right.mul_le_one [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
  mul_le_of_le_one_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one_of_lt_of_le`. -/
@[to_additive Right.add_neg_of_neg_of_nonpos
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg_of_neg_of_nonpos`."]
theorem Right.mul_lt_one_of_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α} (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 :=
  mul_lt_of_lt_one_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one_of_le_of_lt`. -/
@[to_additive Right.add_neg_of_nonpos_of_neg
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg_of_nonpos_of_neg`."]
theorem Right.mul_lt_one_of_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : a ≤ 1) (hb : b < 1) :
    a * b < 1 :=
  mul_lt_of_le_one_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one`. -/
@[to_additive "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg`."]
theorem Right.mul_lt_one [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
  mul_lt_of_lt_one_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.mul_lt_one'`. -/
@[to_additive "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_neg'`."]
theorem Right.mul_lt_one' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
  mul_lt_of_lt_one_of_lt' ha hb

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`,
which assume right covariance. -/


@[to_additive]
theorem le_mul_of_one_le_of_le [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 ≤ a) (hbc : b ≤ c) :
    b ≤ a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mulₓ c).symm
    _ ≤ a * c := mul_le_mul_right' ha c
    

@[to_additive]
theorem lt_mul_of_one_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : 1 < a) (hbc : b ≤ c) :
    b < a * c :=
  calc
    b ≤ c := hbc
    _ = 1 * c := (one_mulₓ c).symm
    _ < a * c := mul_lt_mul_right' ha c
    

@[to_additive]
theorem lt_mul_of_one_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 ≤ a) (hbc : b < c) :
    b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mulₓ c).symm
    _ ≤ a * c := mul_le_mul_right' ha c
    

@[to_additive]
theorem lt_mul_of_one_lt_of_lt [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c : α} (ha : 1 < a) (hbc : b < c) :
    b < a * c :=
  calc
    b < c := hbc
    _ = 1 * c := (one_mulₓ c).symm
    _ < a * c := mul_lt_mul_right' ha c
    

@[to_additive]
theorem lt_mul_of_one_lt_of_lt' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (ha : 1 < a) (hbc : b < c) :
    b < a * c :=
  lt_mul_of_one_le_of_lt ha.le hbc

/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_le_mul`. -/
@[to_additive Right.add_nonneg "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_nonneg`."]
theorem Right.one_le_mul [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  le_mul_of_one_le_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul_of_lt_of_le`. -/
@[to_additive Right.add_pos_of_pos_of_nonneg
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos_of_pos_of_nonneg`."]
theorem Right.one_lt_mul_of_lt_of_le [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α} (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_le ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul_of_le_of_lt`. -/
@[to_additive Right.add_pos_of_nonneg_of_pos
      "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos_of_nonneg_of_pos`."]
theorem Right.one_lt_mul_of_le_of_lt [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b :=
  lt_mul_of_one_le_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul`. -/
@[to_additive Right.add_pos "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos`."]
theorem Right.one_lt_mul [CovariantClass α α (swap (· * ·)) (· < ·)] {a b : α} (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_lt ha hb

/-- Assumes right covariance.
The lemma assuming left covariance is `left.one_lt_mul'`. -/
@[to_additive Right.add_pos' "Assumes right covariance.\nThe lemma assuming left covariance is `left.add_pos'`."]
theorem Right.one_lt_mul' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α} (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_lt' ha hb

alias Left.mul_le_one ← mul_le_one'

alias Left.mul_lt_one_of_le_of_lt ← mul_lt_one_of_le_of_lt

alias Left.mul_lt_one_of_lt_of_le ← mul_lt_one_of_lt_of_le

alias Left.mul_lt_one ← mul_lt_one

alias Left.mul_lt_one' ← mul_lt_one'

attribute [to_additive add_nonpos "**Alias** of `left.add_nonpos`."] mul_le_one'

attribute [to_additive add_neg_of_nonpos_of_neg "**Alias** of `left.add_neg_of_nonpos_of_neg`."] mul_lt_one_of_le_of_lt

attribute [to_additive add_neg_of_neg_of_nonpos "**Alias** of `left.add_neg_of_neg_of_nonpos`."] mul_lt_one_of_lt_of_le

attribute [to_additive "**Alias** of `left.add_neg`."] mul_lt_one

attribute [to_additive "**Alias** of `left.add_neg'`."] mul_lt_one'

alias Left.one_le_mul ← one_le_mul

alias Left.one_lt_mul_of_le_of_lt ← one_lt_mul_of_le_of_lt'

alias Left.one_lt_mul_of_lt_of_le ← one_lt_mul_of_lt_of_le'

alias Left.one_lt_mul ← one_lt_mul'

alias Left.one_lt_mul' ← one_lt_mul''

attribute [to_additive add_nonneg "**Alias** of `left.add_nonneg`."] one_le_mul

attribute [to_additive add_pos_of_nonneg_of_pos "**Alias** of `left.add_pos_of_nonneg_of_pos`."] one_lt_mul_of_le_of_lt'

attribute [to_additive add_pos_of_pos_of_nonneg "**Alias** of `left.add_pos_of_pos_of_nonneg`."] one_lt_mul_of_lt_of_le'

attribute [to_additive add_pos "**Alias** of `left.add_pos`."] one_lt_mul'

attribute [to_additive add_pos' "**Alias** of `left.add_pos'`."] one_lt_mul''

@[to_additive]
theorem lt_of_mul_lt_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b < c) (hle : 1 ≤ b) :
    a < c :=
  (le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
theorem le_of_mul_le_of_one_le_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a * b ≤ c) (hle : 1 ≤ b) :
    a ≤ c :=
  (le_mul_of_one_le_right' hle).trans h

@[to_additive]
theorem lt_of_lt_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a < b * c) (hle : c ≤ 1) :
    a < b :=
  h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
theorem le_of_le_mul_of_le_one_left [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α} (h : a ≤ b * c) (hle : c ≤ 1) :
    a ≤ b :=
  h.trans (mul_le_of_le_one_right' hle)

@[to_additive]
theorem lt_of_mul_lt_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (h : a * b < c)
    (hle : 1 ≤ a) : b < c :=
  (le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
theorem le_of_mul_le_of_one_le_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (h : a * b ≤ c)
    (hle : 1 ≤ a) : b ≤ c :=
  (le_mul_of_one_le_left' hle).trans h

@[to_additive]
theorem lt_of_lt_mul_of_le_one_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (h : a < b * c)
    (hle : b ≤ 1) : a < c :=
  h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
theorem le_of_le_mul_of_le_one_right [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c : α} (h : a ≤ b * c)
    (hle : b ≤ 1) : a ≤ c :=
  h.trans (mul_le_of_le_one_left' hle)

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α]

@[to_additive]
theorem mul_eq_one_iff' [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] {a b : α}
    (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  Iff.intro
    (fun hab : a * b = 1 =>
      have : a ≤ 1 := hab ▸ le_mul_of_le_of_one_le le_rflₓ hb
      have : a = 1 := le_antisymmₓ this ha
      have : b ≤ 1 := hab ▸ le_mul_of_one_le_of_le ha le_rflₓ
      have : b = 1 := le_antisymmₓ this hb
      And.intro ‹a = 1› ‹b = 1›)
    fun ⟨ha', hb'⟩ => by
    rw [ha', hb', mul_oneₓ]

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

theorem exists_square_le [CovariantClass α α (· * ·) (· < ·)] (a : α) : ∃ b : α, b * b ≤ a := by
  by_cases' h : a < 1
  · use a
    have : a * a < a * 1 := mul_lt_mul_left' h a
    rw [mul_oneₓ] at this
    exact le_of_ltₓ this
    
  · use 1
    push_neg  at h
    rwa [mul_oneₓ]
    

end LinearOrderₓ

end MulOneClassₓ

section Semigroupₓ

variable [Semigroupₓ α]

section PartialOrderₓ

variable [PartialOrderₓ α]

/- This is not instance, since we want to have an instance from `left_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/-- A semigroup with a partial order and satisfying `left_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `left_cancel semigroup`. -/
@[to_additive
      "An additive semigroup with a partial order and satisfying `left_cancel_add_semigroup`\n(i.e. `c + a < c + b → a < b`) is a `left_cancel add_semigroup`."]
def Contravariant.toLeftCancelSemigroup [ContravariantClass α α (· * ·) (· ≤ ·)] : LeftCancelSemigroup α :=
  { ‹Semigroupₓ α› with mul_left_cancel := fun a b c => mul_left_cancel'' }

/- This is not instance, since we want to have an instance from `right_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/-- A semigroup with a partial order and satisfying `right_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `right_cancel semigroup`. -/
@[to_additive
      "An additive semigroup with a partial order and satisfying `right_cancel_add_semigroup`\n(`a + c < b + c → a < b`) is a `right_cancel add_semigroup`."]
def Contravariant.toRightCancelSemigroup [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] : RightCancelSemigroup α :=
  { ‹Semigroupₓ α› with mul_right_cancel := fun a b c => mul_right_cancel'' }

@[to_additive]
theorem Left.mul_eq_mul_iff_eq_and_eq [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [ContravariantClass α α (· * ·) (· ≤ ·)] [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α} (hac : a ≤ c)
    (hbd : b ≤ d) : a * b = c * d ↔ a = c ∧ b = d := by
  refine' ⟨fun h => _, fun h => congr_arg2ₓ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, mul_left_cancel'' h⟩
    
  rcases eq_or_lt_of_leₓ hbd with (rfl | hbd)
  · exact ⟨mul_right_cancel'' h, rfl⟩
    
  exact ((Left.mul_lt_mul hac hbd).Ne h).elim

@[to_additive]
theorem Right.mul_eq_mul_iff_eq_and_eq [CovariantClass α α (· * ·) (· ≤ ·)] [ContravariantClass α α (· * ·) (· ≤ ·)]
    [CovariantClass α α (swap (· * ·)) (· < ·)] [ContravariantClass α α (swap (· * ·)) (· ≤ ·)] {a b c d : α}
    (hac : a ≤ c) (hbd : b ≤ d) : a * b = c * d ↔ a = c ∧ b = d := by
  refine' ⟨fun h => _, fun h => congr_arg2ₓ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, mul_left_cancel'' h⟩
    
  rcases eq_or_lt_of_leₓ hbd with (rfl | hbd)
  · exact ⟨mul_right_cancel'' h, rfl⟩
    
  exact ((Right.mul_lt_mul hac hbd).Ne h).elim

alias Left.mul_eq_mul_iff_eq_and_eq ← mul_eq_mul_iff_eq_and_eq

attribute [to_additive] mul_eq_mul_iff_eq_and_eq

end PartialOrderₓ

end Semigroupₓ

section Mono

variable [Mul α] [Preorderₓ α] [Preorderₓ β] {f g : β → α} {s : Set β}

@[to_additive const_add]
theorem Monotone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a

@[to_additive const_add]
theorem MonotoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a

@[to_additive const_add]
theorem Antitone.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => a * f x := fun x y h => mul_le_mul_left' (hf h) a

@[to_additive const_add]
theorem AntitoneOn.const_mul' [CovariantClass α α (· * ·) (· ≤ ·)] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => a * f x) s := fun x hx y hy h => mul_le_mul_left' (hf hx hy h) a

@[to_additive add_const]
theorem Monotone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f) (a : α) :
    Monotone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a

@[to_additive add_const]
theorem MonotoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : MonotoneOn f s) (a : α) :
    MonotoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a

@[to_additive add_const]
theorem Antitone.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f) (a : α) :
    Antitone fun x => f x * a := fun x y h => mul_le_mul_right' (hf h) a

@[to_additive add_const]
theorem AntitoneOn.mul_const' [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : AntitoneOn f s) (a : α) :
    AntitoneOn (fun x => f x * a) s := fun x hx y hy h => mul_le_mul_right' (hf hx hy h) a

/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem Monotone.mul' [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Monotone f)
    (hg : Monotone g) : Monotone fun x => f x * g x := fun x y h => mul_le_mul' (hf h) (hg h)

/-- The product of two monotone functions is monotone. -/
@[to_additive add "The sum of two monotone functions is monotone."]
theorem MonotoneOn.mul' [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    (hf : MonotoneOn f s) (hg : MonotoneOn g s) : MonotoneOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_le_mul' (hf hx hy h) (hg hx hy h)

/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem Antitone.mul' [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)] (hf : Antitone f)
    (hg : Antitone g) : Antitone fun x => f x * g x := fun x y h => mul_le_mul' (hf h) (hg h)

/-- The product of two antitone functions is antitone. -/
@[to_additive add "The sum of two antitone functions is antitone."]
theorem AntitoneOn.mul' [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    (hf : AntitoneOn f s) (hg : AntitoneOn g s) : AntitoneOn (fun x => f x * g x) s := fun x hx y hy h =>
  mul_le_mul' (hf hx hy h) (hg hx hy h)

section Left

variable [CovariantClass α α (· * ·) (· < ·)]

@[to_additive const_add]
theorem StrictMono.const_mul' (hf : StrictMono f) (c : α) : StrictMono fun x => c * f x := fun a b ab =>
  mul_lt_mul_left' (hf ab) c

@[to_additive const_add]
theorem StrictMonoOn.const_mul' (hf : StrictMonoOn f s) (c : α) : StrictMonoOn (fun x => c * f x) s :=
  fun a ha b hb ab => mul_lt_mul_left' (hf ha hb ab) c

@[to_additive const_add]
theorem StrictAnti.const_mul' (hf : StrictAnti f) (c : α) : StrictAnti fun x => c * f x := fun a b ab =>
  mul_lt_mul_left' (hf ab) c

@[to_additive const_add]
theorem StrictAntiOn.const_mul' (hf : StrictAntiOn f s) (c : α) : StrictAntiOn (fun x => c * f x) s :=
  fun a ha b hb ab => mul_lt_mul_left' (hf ha hb ab) c

end Left

section Right

variable [CovariantClass α α (swap (· * ·)) (· < ·)]

@[to_additive add_const]
theorem StrictMono.mul_const' (hf : StrictMono f) (c : α) : StrictMono fun x => f x * c := fun a b ab =>
  mul_lt_mul_right' (hf ab) c

@[to_additive add_const]
theorem StrictMonoOn.mul_const' (hf : StrictMonoOn f s) (c : α) : StrictMonoOn (fun x => f x * c) s :=
  fun a ha b hb ab => mul_lt_mul_right' (hf ha hb ab) c

@[to_additive add_const]
theorem StrictAnti.mul_const' (hf : StrictAnti f) (c : α) : StrictAnti fun x => f x * c := fun a b ab =>
  mul_lt_mul_right' (hf ab) c

@[to_additive add_const]
theorem StrictAntiOn.mul_const' (hf : StrictAntiOn f s) (c : α) : StrictAntiOn (fun x => f x * c) s :=
  fun a ha b hb ab => mul_lt_mul_right' (hf ha hb ab) c

end Right

/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMono.mul' [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
    (hf : StrictMono f) (hg : StrictMono g) : StrictMono fun x => f x * g x := fun a b ab =>
  mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/-- The product of two strictly monotone functions is strictly monotone. -/
@[to_additive add "The sum of two strictly monotone functions is strictly monotone."]
theorem StrictMonoOn.mul' [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
    (hf : StrictMonoOn f s) (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f x * g x) s := fun a ha b hb ab =>
  mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAnti.mul' [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
    (hf : StrictAnti f) (hg : StrictAnti g) : StrictAnti fun x => f x * g x := fun a b ab =>
  mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/-- The product of two strictly antitone functions is strictly antitone. -/
@[to_additive add "The sum of two strictly antitone functions is strictly antitone."]
theorem StrictAntiOn.mul' [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]
    (hf : StrictAntiOn f s) (hg : StrictAntiOn g s) : StrictAntiOn (fun x => f x * g x) s := fun a ha b hb ab =>
  mul_lt_mul_of_lt_of_lt (hf ha hb ab) (hg ha hb ab)

/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strict_mono "The sum of a monotone function and a strictly monotone function is strictly monotone."]
theorem Monotone.mul_strict_mono' [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {f g : β → α} (hf : Monotone f) (hg : StrictMono g) : StrictMono fun x => f x * g x := fun x y h =>
  mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

/-- The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive add_strict_mono "The sum of a monotone function and a strictly monotone function is strictly monotone."]
theorem MonotoneOn.mul_strict_mono' [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {f g : β → α} (hf : MonotoneOn f s) (hg : StrictMonoOn g s) : StrictMonoOn (fun x => f x * g x) s :=
  fun x hx y hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

/-- The product of a antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strict_anti "The sum of a antitone function and a strictly antitone function is strictly antitone."]
theorem Antitone.mul_strict_anti' [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {f g : β → α} (hf : Antitone f) (hg : StrictAnti g) : StrictAnti fun x => f x * g x := fun x y h =>
  mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

/-- The product of a antitone function and a strictly antitone function is strictly antitone. -/
@[to_additive add_strict_anti "The sum of a antitone function and a strictly antitone function is strictly antitone."]
theorem AntitoneOn.mul_strict_anti' [CovariantClass α α (· * ·) (· < ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {f g : β → α} (hf : AntitoneOn f s) (hg : StrictAntiOn g s) : StrictAntiOn (fun x => f x * g x) s :=
  fun x hx y hy h => mul_lt_mul_of_le_of_lt (hf hx hy h.le) (hg hx hy h)

variable [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· < ·)]

/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone "The sum of a strictly monotone function and a monotone function is strictly monotone."]
theorem StrictMono.mul_monotone' (hf : StrictMono f) (hg : Monotone g) : StrictMono fun x => f x * g x := fun x y h =>
  mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

/-- The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive add_monotone "The sum of a strictly monotone function and a monotone function is strictly monotone."]
theorem StrictMonoOn.mul_monotone' (hf : StrictMonoOn f s) (hg : MonotoneOn g s) :
    StrictMonoOn (fun x => f x * g x) s := fun x hx y hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

/-- The product of a strictly antitone function and a antitone function is strictly antitone. -/
@[to_additive add_antitone "The sum of a strictly antitone function and a antitone function is strictly antitone."]
theorem StrictAnti.mul_antitone' (hf : StrictAnti f) (hg : Antitone g) : StrictAnti fun x => f x * g x := fun x y h =>
  mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

/-- The product of a strictly antitone function and a antitone function is strictly antitone. -/
@[to_additive add_antitone "The sum of a strictly antitone function and a antitone function is strictly antitone."]
theorem StrictAntiOn.mul_antitone' (hf : StrictAntiOn f s) (hg : AntitoneOn g s) :
    StrictAntiOn (fun x => f x * g x) s := fun x hx y hy h => mul_lt_mul_of_lt_of_le (hf hx hy h) (hg hx hy h.le)

end Mono

/-- An element `a : α` is `mul_le_cancellable` if `x ↦ a * x` is order-reflecting.
We will make a separate version of many lemmas that require `[contravariant_class α α (*) (≤)]` with
`mul_le_cancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ennreal`, where we can replace the assumption `add_le_cancellable x` by `x ≠ ∞`.
-/
@[to_additive
      " An element `a : α` is `add_le_cancellable` if `x ↦ a + x` is order-reflecting.\nWe will make a separate version of many lemmas that require `[contravariant_class α α (+) (≤)]` with\n`mul_le_cancellable` assumptions instead. These lemmas can then be instantiated to specific types,\nlike `ennreal`, where we can replace the assumption `add_le_cancellable x` by `x ≠ ∞`. "]
def MulLeCancellable [Mul α] [LE α] (a : α) : Prop :=
  ∀ ⦃b c⦄, a * b ≤ a * c → b ≤ c

@[to_additive]
theorem Contravariant.mul_le_cancellable [Mul α] [LE α] [ContravariantClass α α (· * ·) (· ≤ ·)] {a : α} :
    MulLeCancellable a := fun b c => le_of_mul_le_mul_left'

@[to_additive]
theorem mul_le_cancellable_one [Monoidₓ α] [LE α] : MulLeCancellable (1 : α) := fun a b => by
  simpa only [one_mulₓ] using id

namespace MulLeCancellable

@[to_additive]
protected theorem injective [Mul α] [PartialOrderₓ α] {a : α} (ha : MulLeCancellable a) : Injective ((· * ·) a) :=
  fun b c h => le_antisymmₓ (ha h.le) (ha h.Ge)

@[to_additive]
protected theorem inj [Mul α] [PartialOrderₓ α] {a b c : α} (ha : MulLeCancellable a) : a * b = a * c ↔ b = c :=
  ha.Injective.eq_iff

@[to_additive]
protected theorem injective_left [CommSemigroupₓ α] [PartialOrderₓ α] {a : α} (ha : MulLeCancellable a) :
    Injective (· * a) := fun b c h =>
  ha.Injective <| by
    rwa [mul_comm a, mul_comm a]

@[to_additive]
protected theorem inj_left [CommSemigroupₓ α] [PartialOrderₓ α] {a b c : α} (hc : MulLeCancellable c) :
    a * c = b * c ↔ a = b :=
  hc.injective_left.eq_iff

variable [LE α]

@[to_additive]
protected theorem mul_le_mul_iff_left [Mul α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α}
    (ha : MulLeCancellable a) : a * b ≤ a * c ↔ b ≤ c :=
  ⟨fun h => ha h, fun h => mul_le_mul_left' h a⟩

@[to_additive]
protected theorem mul_le_mul_iff_right [CommSemigroupₓ α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b c : α}
    (ha : MulLeCancellable a) : b * a ≤ c * a ↔ b ≤ c := by
  rw [mul_comm b, mul_comm c, ha.mul_le_mul_iff_left]

@[to_additive]
protected theorem le_mul_iff_one_le_right [MulOneClassₓ α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α}
    (ha : MulLeCancellable a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans
    (by
      rw [mul_oneₓ])
    ha.mul_le_mul_iff_left

@[to_additive]
protected theorem mul_le_iff_le_one_right [MulOneClassₓ α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α}
    (ha : MulLeCancellable a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans
    (by
      rw [mul_oneₓ])
    ha.mul_le_mul_iff_left

@[to_additive]
protected theorem le_mul_iff_one_le_left [CommMonoidₓ α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α}
    (ha : MulLeCancellable a) : a ≤ b * a ↔ 1 ≤ b := by
  rw [mul_comm, ha.le_mul_iff_one_le_right]

@[to_additive]
protected theorem mul_le_iff_le_one_left [CommMonoidₓ α] [CovariantClass α α (· * ·) (· ≤ ·)] {a b : α}
    (ha : MulLeCancellable a) : b * a ≤ a ↔ b ≤ 1 := by
  rw [mul_comm, ha.mul_le_iff_le_one_right]

end MulLeCancellable

