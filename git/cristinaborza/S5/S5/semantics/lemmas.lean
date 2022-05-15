import S5.semantics.basic

open Classical

-- General facts about non-modal logical constants
theorem neg_tt_iff_ff { M : model } { w : world } { p : form } : (M, w ⊩ (¬p)) = True ↔ ¬(M, w ⊩ p) := sorry
theorem neg_ff_iff_tt { M : model } { w : world } { p : form } : (M, w ⊩ p) = True ↔ ¬(M, w ⊩ (¬p)) := sorry

theorem impl_iff_implies { M : model } { w : world } {p q : form } :
  (M, w ⊩ (p → q)) = True ↔ ((M, w ⊩ p) → (M, w ⊩ q)) := sorry


theorem impl_tt_iff_ff_or_tt { M : model } { w : world } { p q : form } :
  (M, w ⊩ (p → q)) = true ↔ (¬(M, w ⊩ p)) ∨ (M, w ⊩ q) = True := sorry 

theorem ff_or_tt_and_tt_implies_tt_right { M : model } { w : world } { p q : form } :
  ((¬(M, w ⊩ p)) ∨ (M, w ⊩ q) = True) → ((M, w ⊩ p) = True) → ((M, w ⊩ q) = True) := sorry 

theorem bot_is_insatisf { w : world } : ¬∃ (M : model), (M, w ⊩ ⊥) = True := sorry 

--  Modal logical constants (=>)
theorem forall_wrld_tt_nec_tt { M : model } { w : world } { p : form } : 
  (∀ v, (v ∈ M.worlds) → (w ∈ M.worlds) → (M.access w v) → ((M, v ⊩ p) = True) → ((M, w ⊩ (□p)) = True)) := sorry

theorem exists_wlrd_tt_pos_tt { M : model } { w : world } { p : form } : 
  (∃ v, (v ∈ M.worlds) → (w ∈ M.worlds) → (M.access w v = True) → ((M, v ⊩ p) = True)) → ((M, w ⊩ ⋄p) = True) := sorry

-- Modal logical constants (<=)
theorem nec_tt_forall_wrld_tt { M : model } { w : world } { p : form } :
  ((M, w ⊩ (□p)) = True) → (∀ v, (v ∈ M.worlds) → (w ∈ M.worlds) → (M.access w v) → ((M, v ⊩ p) = True)) := sorry

theorem pos_tt_exists_wlrd_tt { M : model } { w : world } { p : form } :
  ((M, w ⊩ (□p)) = True) → (∃ v, (v ∈ M.worlds) → (w ∈ M.worlds) → (M.access w v) → ((M, v ⊩ p) = True)) := sorry

theorem pos_ff_forall_wrld_ff { M : model } { w : world } { p : form } :
  ((M, w ⊩ (⋄p)) = False) →(∀ v, (v ∈ M.worlds) → (w ∈ M.worlds) → (M.access w v) → ((M, v ⊩ p) = False)) := sorry

-- Some facts about PL
theorem is_true_pl1 { M : model } { w : world } { p q : form } : (M, w ⊩ p → (q → p)) = True := sorry
theorem is_true_pl2 { M : model } { w : world } { p q r : form } : (M, w ⊩ (p → (q → r)) → ((p → q) → (p → r))) := sorry
theorem is_true_pl3 { M : model } { w : world } { p q : form } : (M, w ⊩ (((¬p) → (¬q)) → (((¬p) → q) → p))) := sorry

-- Some facts about K
theorem nec_impl_to_nec_to_nec { M : model } { w : world } { p q : form } : 
  ((M, w ⊩ □(p → q)) = True) → ((M, w ⊩ □p) = True) → ((M, w ⊩ □q) = True) := sorry

theorem nec_nec_to_nec_impl { M : model } { w : world } { p q : form } :
  ((M, w ⊩ □p) = True) → ((M, w ⊩ □q) = True) → ((M, w ⊩ □(p → q)) = True) := sorry 

theorem nec_impl_to_nec_impl_nec { M : model } { w : world } { p q : form } :
  ((M, w ⊩ □(p → q)) = True) → (((M, w ⊩ □p) = False) ∨ ((M, w ⊩ □q) = True)) := sorry

theorem is_true_k { M : model } { w : world } { p q : form } :
  (M, w ⊩ (□(p → q)) → ((□p) → □q)) = True := sorry
--impl_iff_implies.2 (λ h => impl_tt_iff_ff_or_tt.2 (nec_impl_to_nec_impl_nec h))


-- Some facts about T
theorem nec_to_tt { M : model } { w : world } { wm : w ∈ M.worlds } { p : form } :
  (M, w ⊩ □p) = True → (M, w ⊩ p) = True := sorry 

theorem is_true_t { M : model } { w : world } { wm : w ∈ M.worlds } { p : form } : 
  (M, w ⊩ (□p) → p) = True := by 
  apply impl_iff_implies.2
  apply nec_to_tt
  repeat assumption

-- Some facts about S4
theorem nec_to_nec_of_nec { M : model } { w : world } { p : form } : 
  (M, w ⊩ □p) = True → (M, w ⊩ □□p) = True := sorry

theorem is_true_s4 { M : model } { w : world } { p : form } : (M, w ⊩ (□p) → □□p) = True := by 
  apply impl_iff_implies.2
  apply nec_to_nec_of_nec

-- General facts about contexts
theorem ctx_tt_iff_mem_tt { Γ : ctx } { M : model } { w : world } :
  (M, w ⊩ Γ) = True ↔ (∀ p, (p ∈ Γ) → (M, w ⊩ p) = True) := sorry 

theorem mem_tt_to_ctx_tt (Γ : ctx) { M : model } { w : world } :
  (∀ (p : form), (h : p ∈ Γ) → (M, w ⊩ p) = True) → (M, w ⊩ Γ) = True :=
  ctx_tt_iff_mem_tt.2

theorem ctx_tt_to_mem_tt { Γ : ctx } { M : model } { w : world } { p : form } :
  (M, w ⊩ Γ) = True → (p ∈ Γ) → (M, w ⊩ p) = True := by
  intro
  apply ctx_tt_iff_mem_tt.1
  assumption

-- The empty context
theorem empty_ctx_tt { M : model } { w : world } : (M, w ⊩ []) = True := by
  apply ctx_tt_iff_mem_tt.2
  intro
  sorry
  --apply False.elim
  --assumption

