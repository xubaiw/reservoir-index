import S5.soundness 

open Classical
open prf 

def is_consistent (Γ : ctx) := Γ ⊬ₛ₅ ⊥

theorem consist_not_of_not_prf { Γ : ctx } { p : form } : (Γ ⊬ₛ₅ p) → is_consistent (Γ ∪ ¬p) := 
  fun hnp hc => hnp (mp dne (deduction hc))

theorem not_prf_of_consist_not { Γ : ctx } { p : form } : is_consistent (Γ ∪ ¬p) → (Γ ⊬ₛ₅ p) := 
  fun h c => h (conv_deduction (mp dni c))

-- Other notable properties of consistency

theorem consist_of_not_prf { Γ : ctx } { p : form } : (Γ ⊬ₛ₅ p) → is_consistent Γ := sorry
--  fun nhp nc => nhp (False.elim nc) 

theorem inconsist_to_neg_consist { Γ : ctx } { p : form } :
  is_consistent Γ → (¬ is_consistent (Γ ∪ p)) → is_consistent (Γ ∪ ¬p) := by
  intros c nc hp 
  apply c
  apply mp
  apply deduction
  apply byContradiction nc
  apply mp dne
  exact (deduction hp)

theorem inconsist_of_neg_to_consist { Γ : ctx } { p : form } : 
  is_consistent Γ → (¬ is_consistent (Γ ∪ ¬p)) → is_consistent (Γ ∪ p) := by 
  intros c nc hp
  apply c
  apply mp
  { apply deduction (byContradiction nc) }
  { exact deduction hp }

theorem consist_fst { Γ : ctx } { p : form } : is_consistent (Γ ∪ p) → is_consistent Γ := 
  fun hc hn => hc (weak hn)

-- Consistent context extensions
theorem consist_ext { Γ : ctx } { p : form } : is_consistent Γ → (Γ ⊬ₛ₅ ¬p) → is_consistent (Γ ∪ p) := by
  intros c np hn
  apply np (deduction hn)

theorem inconsist_ext_to_inconsist { Γ : ctx } { p : form } : 
  (And (is_consistent (Γ ∪ p)) (¬is_consistent (Γ ∪ ¬p))) → (¬is_consistent Γ) := sorry
-- by
--   intros h nc
--   have h₁ : ((Γ ∪ p) ⊢ₛ₅ ⊥) := byContradiction (And.left h)
--   have h₂ : ((Γ ∪ ¬p) ⊢ₛ₅ ⊥) := byContradiction (And.right h)
--   apply nc
--   apply mp (deduction h₁)
--   apply mp dne (deduction h₂)

theorem consist_to_consist_ext { Γ : ctx } { p : form } : 
  is_consistent Γ → (is_consistent (Γ ∪ p) ∨ is_consistent (Γ ∪ ¬p)) := sorry
  -- intro c
  -- apply byContradiction
  -- intro h 
  -- apply absurd c
  -- apply inconsist_ext_to_inconsist
  -- apply (decidable.not_or_iff_and_not _ _).1
  -- apply h
  -- repeat apply (prop_decidable _)

theorem pos_inconsist_ext { Γ : ctx } { p : form } (c : is_consistent Γ) :
  (p ∈ Γ) → (is_consistent (Γ ∪ p)) → (¬p) ∈ Γ := sorry
-- by 
--   intros hp hn
--   apply False.elim
--   apply c
--   apply mp
--   apply deduction (byContradiction hn)
--   apply ax hp

theorem neg_inconsist_ext { Γ : ctx } { p : form } (c : is_consistent Γ) :
  ((¬p) ∈ Γ) → (¬is_consistent (Γ ∪ p)) → p ∈ Γ := sorry 


-- Context extensions of subcontexts
-- theorem sub_preserves_consist { Γ Δ : ctx } :
--   (is_consistent) Γ → (is_consistent Δ) → (Δ ⊆ Γ) → is_consistent (Γ ⊔ Δ) :=
-- by intros c1 c2 s nc; apply c1; exact (subctx_contr s nc)

-- Contradictions & interpretations

theorem tt_to_const { Γ : ctx } { M : model }:
  (w ∈ M.worlds) → ((M, w ⊩ Γ) = True) → (is_consistent Γ) := by
  intros w h hin
  cases (soundness hin)
  apply bot_is_insatisf
  apply Exists.intro
  sorry 
  --rename_i 
  -- refine (_ M w _ h)
  repeat assumption