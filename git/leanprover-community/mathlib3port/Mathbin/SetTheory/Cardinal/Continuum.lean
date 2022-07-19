/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of continuum

In this file we define `cardinal.continuum` (notation: `𝔠`, localized in `cardinal`) to be `2 ^ ℵ₀`.
We also prove some `simp` lemmas about cardinal arithmetic involving `𝔠`.

## Notation

- `𝔠` : notation for `cardinal.continuum` in locale `cardinal`.
-/


namespace Cardinal

universe u v

open Cardinal

/-- Cardinality of continuum. -/
def continuum : Cardinal.{u} :=
  2 ^ aleph_0.{u}

-- mathport name: «expr𝔠»
localized [Cardinal] notation "𝔠" => Cardinal.continuum

@[simp]
theorem two_power_aleph_0 : 2 ^ aleph_0.{u} = continuum.{u} :=
  rfl

@[simp]
theorem lift_continuum : lift.{v} 𝔠 = 𝔠 := by
  rw [← two_power_aleph_0, lift_two_power, lift_aleph_0, two_power_aleph_0]

/-!
### Inequalities
-/


theorem aleph_0_lt_continuum : ℵ₀ < 𝔠 :=
  cantor ℵ₀

theorem aleph_0_le_continuum : ℵ₀ ≤ 𝔠 :=
  aleph_0_lt_continuum.le

theorem nat_lt_continuum (n : ℕ) : ↑n < 𝔠 :=
  (nat_lt_aleph_0 n).trans aleph_0_lt_continuum

theorem mk_set_nat : # (Set ℕ) = 𝔠 := by
  simp

theorem continuum_pos : 0 < 𝔠 :=
  nat_lt_continuum 0

theorem continuum_ne_zero : 𝔠 ≠ 0 :=
  continuum_pos.ne'

theorem aleph_one_le_continuum : aleph 1 ≤ 𝔠 := by
  rw [← succ_aleph_0]
  exact Order.succ_le_of_lt aleph_0_lt_continuum

@[simp]
theorem continuum_to_nat : continuum.toNat = 0 :=
  to_nat_apply_of_aleph_0_le aleph_0_le_continuum

@[simp]
theorem continuum_to_part_enat : continuum.toPartEnat = ⊤ :=
  to_part_enat_apply_of_aleph_0_le aleph_0_le_continuum

/-!
### Addition
-/


@[simp]
theorem aleph_0_add_continuum : ℵ₀ + 𝔠 = 𝔠 :=
  add_eq_right aleph_0_le_continuum aleph_0_le_continuum

@[simp]
theorem continuum_add_aleph_0 : 𝔠 + ℵ₀ = 𝔠 :=
  (add_commₓ _ _).trans aleph_0_add_continuum

@[simp]
theorem continuum_add_self : 𝔠 + 𝔠 = 𝔠 :=
  add_eq_right aleph_0_le_continuum le_rfl

@[simp]
theorem nat_add_continuum (n : ℕ) : ↑n + 𝔠 = 𝔠 :=
  add_eq_right aleph_0_le_continuum (nat_lt_continuum n).le

@[simp]
theorem continuum_add_nat (n : ℕ) : 𝔠 + n = 𝔠 :=
  (add_commₓ _ _).trans (nat_add_continuum n)

/-!
### Multiplication
-/


@[simp]
theorem continuum_mul_self : 𝔠 * 𝔠 = 𝔠 :=
  mul_eq_left aleph_0_le_continuum le_rfl continuum_ne_zero

@[simp]
theorem continuum_mul_aleph_0 : 𝔠 * ℵ₀ = 𝔠 :=
  mul_eq_left aleph_0_le_continuum aleph_0_le_continuum aleph_0_ne_zero

@[simp]
theorem aleph_0_mul_continuum : ℵ₀ * 𝔠 = 𝔠 :=
  (mul_comm _ _).trans continuum_mul_aleph_0

@[simp]
theorem nat_mul_continuum {n : ℕ} (hn : n ≠ 0) : ↑n * 𝔠 = 𝔠 :=
  mul_eq_right aleph_0_le_continuum (nat_lt_continuum n).le (Nat.cast_ne_zero.2 hn)

@[simp]
theorem continuum_mul_nat {n : ℕ} (hn : n ≠ 0) : 𝔠 * n = 𝔠 :=
  (mul_comm _ _).trans (nat_mul_continuum hn)

/-!
### Power
-/


@[simp]
theorem aleph_0_power_aleph_0 : aleph_0.{u} ^ aleph_0.{u} = 𝔠 :=
  power_self_eq le_rfl

@[simp]
theorem nat_power_aleph_0 {n : ℕ} (hn : 2 ≤ n) : (n ^ aleph_0.{u} : Cardinal.{u}) = 𝔠 :=
  nat_power_eq le_rfl hn

@[simp]
theorem continuum_power_aleph_0 : continuum.{u} ^ aleph_0.{u} = 𝔠 := by
  rw [← two_power_aleph_0, ← power_mul, mul_eq_left le_rfl le_rfl aleph_0_ne_zero]

end Cardinal

