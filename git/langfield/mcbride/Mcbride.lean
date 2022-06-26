-- An exploration of examples from Conor McBride's CS410: Advanced Functional
-- Programming. Originally written in Agda, translated to Lean 4.

universe u

inductive Zero : Type u where
#check Zero

structure One : Type where
#check One
#check One.mk
#check ({ } : One)

-- This is Conor's `+`.
inductive Either (S : Type u) (T : Type u) : Type u where
  | inl : S → Either S T
  | inr : T → Either S T

structure Product (S : Type u) (T : Type u) : Type u where
  fst : S
  snd : T

theorem productIsCommutative : Product α β → Product β α := by
  intro h
  let a := h.fst
  let b := h.snd
  apply Product.mk
  assumption
  assumption

theorem eitherIsCommutative : Either A B → Either B A := by
  intro h
  cases h
  apply Either.inr
  assumption
  apply Either.inl
  assumption

-- An alternate proof with pattern matching, using Lean 4's built in `Sum` type
-- instead.
--
-- The bullet notation `. <tactics>` is just a way of structuring the proof,
-- i.e. starting work on a specific subgoal and increasing the indentation
-- level. It is not an operator, and removing the bullets and the indentation
-- will result in an identical proof. See TPIL, specifically, the 'Tactics'
-- section.
theorem sumIsCommutative {α β : Type u} : Sum α β → Sum β α := by
  intro h
  cases h
  . apply Sum.inr
    assumption
  . apply Sum.inl
    assumption


theorem eitherIsAssociative : Either (Either α β) γ → Either α (Either β γ) := by
  intro h
  cases h
  case inl h =>
    cases h
    apply Either.inl
    assumption
    apply Either.inr
    apply Either.inl
    assumption
  case inr h =>
    apply Either.inr
    apply Either.inr
    assumption

#check eitherIsAssociative


theorem vBad : Zero → α := by
  intro z
  cases z


def hello := "world"
