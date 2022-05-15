import S5.sematics.basic

open Classical

theorem neg_tt_iff_ff { M : model } { w : world } { p : form } : (M, w ⊩ (¬p)) = True ↔ ¬(M, w ⊩ p) := sorry 
theorem neg_ff_iff_tt { M : model } { w : world } { p : form } : (M, w ⊩ p) = True ↔ ¬(M, w ⊩ (¬p)) := sorry

theorem impl_iff_implies { M : model } { w : world } {p q : form } :
  (M, w ⊩ (p → q)) = True ↔ ((M, w ⊩ p) → (M, w ⊩ q)) := sorry


theorem impl_tt_iff_ff_or_tt { M : model } { w : world } { p q : form } :
  (M, w ⊩ (p → q)) = true ↔ (¬(M, w ⊩ p)) ∨ (M, w ⊩ q) = True := sorry 

theorem ff_or_tt_and_tt_implies_tt_right { M : model } { w : world } { p q : form } :
  ((¬(M, w ⊩ p)) ∨ (M, w ⊩ q) = True) → ((M, w ⊩ p) = True) → ((M, w ⊩ q) = True) := sorry 

theorem bot_is_insatisf { w : world } : ¬∃ (M : model), (M, w ⊩ ⊥) = True := sorry 

theorem forall_wrld_tt_nec_tt { M : model } { w : world } { p : form } : 
  (∀ v, (v ∈ M.worlds) → (w ∈ M.worlds) → (M.access w v) → ((M, v ⊩ p) = True) → ((M, w ⊩ (□p)) = True)) := sorry

-- theorem exists_wlrd_tt_pos_tt { M : model } { w : world } { p : form } : 
--   (∃ v, (v ∈ M.worlds) → ((w ∈ M.worlds) ∧ (M.access w v = True) ∧ ((M, v ⊩ p) = True))) → (M, w ⊩ ⋄p) = True := sorry

-- Modal logical constants (<=)