/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Order.Basic
import Mathbin.Order.Monotone

/-!

# Covariants and contravariants

This file contains general lemmas and instances to work with the interactions between a relation and
an action on a Type.

The intended application is the splitting of the ordering from the algebraic assumptions on the
operations in the `ordered_[...]` hierarchy.

The strategy is to introduce two more flexible typeclasses, `covariant_class` and
`contravariant_class`:

* `covariant_class` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `contravariant_class` models the implication `a * b < a * c → b < c`.

Since `co(ntra)variant_class` takes as input the operation (typically `(+)` or `(*)`) and the order
relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.

The general approach is to formulate the lemma that you are interested in and prove it, with the
`ordered_[...]` typeclass of your liking.  After that, you convert the single typeclass,
say `[ordered_cancel_monoid M]`, into three typeclasses, e.g.
`[left_cancel_semigroup M] [partial_order M] [covariant_class M M (function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!

Note that it is possible to combine several co(ntra)variant_class assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[covariant_class M M (*) (≤)] [contravariant_class M M (*) (<)]`
on top of order/algebraic assumptions.

A formal remark is that normally `covariant_class` uses the `(≤)`-relation, while
`contravariant_class` uses the `(<)`-relation. This need not be the case in general, but seems to be
the most common usage. In the opposite direction, the implication
```lean
[semigroup α] [partial_order α] [contravariant_class α α (*) (≤)] => left_cancel_semigroup α
```
holds -- note the `co*ntra*` assumption on the `(≤)`-relation.

# Formalization notes

We stick to the convention of using `function.swap (*)` (or `function.swap (+)`), for the
typeclass assumptions, since `function.swap` is slightly better behaved than `flip`.
However, sometimes as a **non-typeclass** assumption, we prefer `flip (*)` (or `flip (+)`),
as it is easier to use. -/


-- TODO: convert `has_exists_mul_of_le`, `has_exists_add_of_le`?
-- TODO: relationship with `con/add_con`
-- TODO: include equivalence of `left_cancel_semigroup` with
-- `semigroup partial_order contravariant_class α α (*) (≤)`?
-- TODO : use ⇒, as per Eric's suggestion?  See
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered.20stuff/near/236148738
-- for a discussion.
open Function

section Variants

variable {M N : Type _} (μ : M → N → N) (r : N → N → Prop)

variable (M N)

/-- `covariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `covariant_class` doc-string for its meaning. -/
def Covariant : Prop :=
  ∀ m {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

/-- `contravariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `contravariant_class` doc-string for its meaning. -/
def Contravariant : Prop :=
  ∀ m {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂

/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`covariant_class` says that "the action `μ` preserves the relation `r`."

More precisely, the `covariant_class` is a class taking two Types `M N`, together with an "action"
`μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
`(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)`,
obtained from `(n₁, n₂)` by acting upon it by `m`.

If `m : M` and `h : r n₁ n₂`, then `covariant_class.elim m h : r (μ m n₁) (μ m n₂)`.
-/
@[protect_proj]
class CovariantClass : Prop where
  elim : Covariant M N μ r

/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`contravariant_class` says that "if the result of the action `μ` on a pair satisfies the
relation `r`, then the initial pair satisfied the relation `r`."

More precisely, the `contravariant_class` is a class taking two Types `M N`, together with an
"action" `μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the
assertion that for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
`r` also holds for the pair `(n₁, n₂)`.

If `m : M` and `h : r (μ m n₁) (μ m n₂)`, then `contravariant_class.elim m h : r n₁ n₂`.
-/
@[protect_proj]
class ContravariantClass : Prop where
  elim : Contravariant M N μ r

theorem rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b :=
  ⟨ContravariantClass.elim _, CovariantClass.elim _⟩

section flip

variable {M N μ r}

theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) := fun a b c hbc => h a hbc

theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) := fun a b c hbc => h a hbc

end flip

section Covariant

variable {M N μ r} [CovariantClass M N μ r]

theorem act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b) :=
  CovariantClass.elim _ ab

@[to_additive]
theorem Groupₓ.covariant_iff_contravariant [Groupₓ N] : Covariant N N (· * ·) r ↔ Contravariant N N (· * ·) r := by
  refine' ⟨fun h a b c bc => _, fun h a b c bc => _⟩
  · rw [← inv_mul_cancel_leftₓ a b, ← inv_mul_cancel_leftₓ a c]
    exact h a⁻¹ bc
    
  · rw [← inv_mul_cancel_leftₓ a b, ← inv_mul_cancel_leftₓ a c] at bc
    exact h a⁻¹ bc
    

@[to_additive]
instance (priority := 100) Groupₓ.covconv [Groupₓ N] [CovariantClass N N (· * ·) r] :
    ContravariantClass N N (· * ·) r :=
  ⟨Groupₓ.covariant_iff_contravariant.mp CovariantClass.elim⟩

@[to_additive]
theorem Groupₓ.covariant_swap_iff_contravariant_swap [Groupₓ N] :
    Covariant N N (swap (· * ·)) r ↔ Contravariant N N (swap (· * ·)) r := by
  refine' ⟨fun h a b c bc => _, fun h a b c bc => _⟩
  · rw [← mul_inv_cancel_rightₓ b a, ← mul_inv_cancel_rightₓ c a]
    exact h a⁻¹ bc
    
  · rw [← mul_inv_cancel_rightₓ b a, ← mul_inv_cancel_rightₓ c a] at bc
    exact h a⁻¹ bc
    

@[to_additive]
instance (priority := 100) Groupₓ.covconv_swap [Groupₓ N] [CovariantClass N N (swap (· * ·)) r] :
    ContravariantClass N N (swap (· * ·)) r :=
  ⟨Groupₓ.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim⟩

section IsTrans

variable [IsTrans N r] (m n : M) {a b c d : N}

--  Lemmas with 3 elements.
theorem act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  trans (act_rel_act_of_rel m ab) rl

theorem rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) :=
  trans rr (act_rel_act_of_rel _ ab)

end IsTrans

end Covariant

--  Lemma with 4 elements.
section MEqN

variable {M N μ r} {mu : N → N → N} [IsTrans N r] [CovariantClass N N mu r] [CovariantClass N N (swap mu) r]
  {a b c d : N}

theorem act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d) :=
  trans (act_rel_act_of_rel c ab : _) (act_rel_act_of_rel b cd)

end MEqN

section Contravariant

variable {M N μ r} [ContravariantClass M N μ r]

theorem rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) : r a b :=
  ContravariantClass.elim _ ab

section IsTrans

variable [IsTrans N r] (m n : M) {a b c d : N}

--  Lemmas with 3 elements.
theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) : r (μ m a) c :=
  trans ab (rel_of_act_rel_act m rl)

theorem rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) : r a (μ m c) :=
  trans (rel_of_act_rel_act m ab) rr

end IsTrans

end Contravariant

section Monotone

variable {α : Type _} {M N μ} [Preorderₓ α] [Preorderₓ N]

variable {f : N → α}

/-- The partial application of a constant to a covariant operator is monotone. -/
theorem Covariant.monotone_of_const [CovariantClass M N μ (· ≤ ·)] (m : M) : Monotone (μ m) := fun a b ha =>
  CovariantClass.elim m ha

/-- A monotone function remains monotone when composed with the partial application
of a covariant operator. E.g., `∀ (m : ℕ), monotone f → monotone (λ n, f (m + n))`. -/
theorem Monotone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Monotone f) (m : M) :
    Monotone fun n => f (μ m n) :=
  hf.comp <| Covariant.monotone_of_const m

/-- Same as `monotone.covariant_of_const`, but with the constant on the other side of
the operator.  E.g., `∀ (m : ℕ), monotone f → monotone (λ n, f (n + m))`. -/
theorem Monotone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)] (hf : Monotone f) (m : N) :
    Monotone fun n => f (μ n m) :=
  hf.comp <| Covariant.monotone_of_const m

/-- Dual of `monotone.covariant_of_const` -/
theorem Antitone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Antitone f) (m : M) :
    Antitone fun n => f (μ m n) :=
  hf.comp_monotone <| Covariant.monotone_of_const m

/-- Dual of `monotone.covariant_of_const'` -/
theorem Antitone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)] (hf : Antitone f) (m : N) :
    Antitone fun n => f (μ n m) :=
  hf.comp_monotone <| Covariant.monotone_of_const m

end Monotone

theorem covariant_le_of_covariant_lt [PartialOrderₓ N] : Covariant M N μ (· < ·) → Covariant M N μ (· ≤ ·) := by
  refine' fun h a b c bc => _
  rcases le_iff_eq_or_lt.mp bc with (rfl | bc)
  · exact rfl.le
    
  · exact (h _ bc).le
    

theorem contravariant_lt_of_contravariant_le [PartialOrderₓ N] :
    Contravariant M N μ (· ≤ ·) → Contravariant M N μ (· < ·) := by
  refine' fun h a b c bc => lt_iff_le_and_ne.mpr ⟨h a bc.le, _⟩
  rintro rfl
  exact lt_irreflₓ _ bc

theorem covariant_le_iff_contravariant_lt [LinearOrderₓ N] : Covariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) :=
  ⟨fun h a b c bc => not_leₓ.mp fun k => not_leₓ.mpr bc (h _ k), fun h a b c bc =>
    not_ltₓ.mp fun k => not_ltₓ.mpr bc (h _ k)⟩

theorem covariant_lt_iff_contravariant_le [LinearOrderₓ N] : Covariant M N μ (· < ·) ↔ Contravariant M N μ (· ≤ ·) :=
  ⟨fun h a b c bc => not_ltₓ.mp fun k => not_ltₓ.mpr bc (h _ k), fun h a b c bc =>
    not_leₓ.mp fun k => not_leₓ.mpr bc (h _ k)⟩

@[to_additive]
theorem covariant_flip_mul_iff [CommSemigroupₓ N] : Covariant N N (flip (· * ·)) r ↔ Covariant N N (· * ·) r := by
  rw [IsSymmOp.flip_eq]

@[to_additive]
theorem contravariant_flip_mul_iff [CommSemigroupₓ N] :
    Contravariant N N (flip (· * ·)) r ↔ Contravariant N N (· * ·) r := by
  rw [IsSymmOp.flip_eq]

@[to_additive]
instance contravariant_mul_lt_of_covariant_mul_le [Mul N] [LinearOrderₓ N] [CovariantClass N N (· * ·) (· ≤ ·)] :
    ContravariantClass N N (· * ·)
      (· < ·) where elim := (covariant_le_iff_contravariant_lt N N (· * ·)).mp CovariantClass.elim

@[to_additive]
instance covariant_mul_lt_of_contravariant_mul_le [Mul N] [LinearOrderₓ N] [ContravariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (· * ·)
      (· < ·) where elim := (covariant_lt_iff_contravariant_le N N (· * ·)).mpr ContravariantClass.elim

@[to_additive]
instance covariant_swap_mul_le_of_covariant_mul_le [CommSemigroupₓ N] [LE N] [CovariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (swap (· * ·)) (· ≤ ·) where elim := (covariant_flip_mul_iff N (· ≤ ·)).mpr CovariantClass.elim

@[to_additive]
instance contravariant_swap_mul_le_of_contravariant_mul_le [CommSemigroupₓ N] [LE N]
    [ContravariantClass N N (· * ·) (· ≤ ·)] :
    ContravariantClass N N (swap (· * ·))
      (· ≤ ·) where elim := (contravariant_flip_mul_iff N (· ≤ ·)).mpr ContravariantClass.elim

@[to_additive]
instance contravariant_swap_mul_lt_of_contravariant_mul_lt [CommSemigroupₓ N] [LT N]
    [ContravariantClass N N (· * ·) (· < ·)] :
    ContravariantClass N N (swap (· * ·))
      (· < ·) where elim := (contravariant_flip_mul_iff N (· < ·)).mpr ContravariantClass.elim

@[to_additive]
instance covariant_swap_mul_lt_of_covariant_mul_lt [CommSemigroupₓ N] [LT N] [CovariantClass N N (· * ·) (· < ·)] :
    CovariantClass N N (swap (· * ·)) (· < ·) where elim := (covariant_flip_mul_iff N (· < ·)).mpr CovariantClass.elim

@[to_additive]
instance LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le [LeftCancelSemigroup N] [PartialOrderₓ N]
    [CovariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (· * ·) (· < ·) where elim := fun a b c bc => by
    cases' lt_iff_le_and_ne.mp bc with bc cb
    exact lt_iff_le_and_ne.mpr ⟨CovariantClass.elim a bc, (mul_ne_mul_right a).mpr cb⟩

@[to_additive]
instance RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le [RightCancelSemigroup N] [PartialOrderₓ N]
    [CovariantClass N N (swap (· * ·)) (· ≤ ·)] :
    CovariantClass N N (swap (· * ·)) (· < ·) where elim := fun a b c bc => by
    cases' lt_iff_le_and_ne.mp bc with bc cb
    exact lt_iff_le_and_ne.mpr ⟨CovariantClass.elim a bc, (mul_ne_mul_left a).mpr cb⟩

@[to_additive]
instance LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_lt [LeftCancelSemigroup N] [PartialOrderₓ N]
    [ContravariantClass N N (· * ·) (· < ·)] :
    ContravariantClass N N (· * ·) (· ≤ ·) where elim := fun a b c bc => by
    cases' le_iff_eq_or_lt.mp bc with h h
    · exact ((mul_right_injₓ a).mp h).le
      
    · exact (ContravariantClass.elim _ h).le
      

@[to_additive]
instance RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt [RightCancelSemigroup N]
    [PartialOrderₓ N] [ContravariantClass N N (swap (· * ·)) (· < ·)] :
    ContravariantClass N N (swap (· * ·)) (· ≤ ·) where elim := fun a b c bc => by
    cases' le_iff_eq_or_lt.mp bc with h h
    · exact ((mul_left_injₓ a).mp h).le
      
    · exact (ContravariantClass.elim _ h).le
      

end Variants

