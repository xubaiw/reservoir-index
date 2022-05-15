import S5.syntax.basic

open prf 

-- Identity implication
theorem idd { p : form } { Γ : ctx } : Γ ⊢ₛ₅ p → p := by
  apply mp
  case hpq => 
    apply mp 
    case hpq => exact @pl2 Γ p (p → p) p 
    case hp => exact @pl1 Γ p (p → p)
  case hp => exact @pl1 Γ p p

-- Deduction metatheorem
theorem deduction { Γ : ctx } { p q : form } : ((Γ ∪ p) ⊢ₛ₅ q) → (Γ ⊢ₛ₅ p → q) := by
  intros h 
  cases h
  {
    rename_i h₀;
    cases h₀;
    { exact idd }
    {
      rename_i h₁;
      exact mp pl1 (ax h₁)
    }
  } 
  { exact mp pl1 pl1 }
  { exact mp pl1 pl2 }
  { exact mp pl1 pl3 }
  {
    sorry
  }
  { exact mp pl1 k }
  { exact mp pl1 t }
  { exact mp pl1 s4 }
  { exact mp pl1 s5 }
  { 
    rename_i h₀;
    exact mp pl1 (nec h₀)
  }

-- Structural rules
theorem sub_weak { Γ Δ : ctx } { p : form } : (Δ ⊢ₛ₅ p) → (Δ ⊆ Γ) → (Γ ⊢ₛ₅ p) := by 
  intros h₀ h₁
  induction h₀
  {
    rename_i Δ p h₂;
    apply ax;
    sorry
    -- apply ax;
  }
  { exact pl1 }
  { exact pl2 }
  { exact pl3 }
  { sorry }
  { exact k }
  { exact t }
  { exact s4 }
  { exact s5 }
  {  
    rename_i h₂ h₃;
    exact nec h₂;
  }

theorem weak { Γ : ctx } { p q : form } :(Γ ⊢ₛ₅ p) → ((Γ ∪ q) ⊢ₛ₅ p) := by
  intros h 
  induction h 
  { sorry }
  { exact pl1 }
  { exact pl2 }
  { exact pl3 }
  { sorry }
  { exact k }
  { exact t }
  { exact s4 }
  { exact s5 }
  {  
    rename_i h₀ h₁;
    exact nec h₀;
  }

theorem contr { Γ : ctx } { p q : form } : (((Γ ∪ p) ∪ p) ⊢ₛ₅ q) → ((Γ ∪ p) ⊢ₛ₅ q) := by
  intros h 
  cases h 
  {  
    apply ax;
    rename_i h₀;
    sorry
  }
  { exact pl1 }
  { exact pl2 }
  { exact pl3 }
  { sorry }
  { exact k }
  { exact t }
  { exact s4 }
  { exact s5 }
  {  
    rename_i h₀;
    exact nec h₀;
  }

theorem exg { Γ : ctx } { p q r : form } : (((Γ ∪ p) ∪ q) ⊢ₛ₅ r) → (((Γ ∪ q) ∪ p) ⊢ₛ₅ r) := sorry

theorem subctx_ax { Γ Δ : ctx } { p : form } : (Δ ⊆ Γ) → (Δ ⊢ₛ₅ p) → (Γ ⊢ₛ₅ p) := by
  intros s h 
  induction h 
  { sorry }
  { exact pl1 }
  { exact pl2 }
  { exact pl3 }
  { sorry }
  { exact k }
  { exact t }
  { exact s4 }
  { exact s5 }
  {  
    rename_i h₀ h₁;
    exact nec h₀;
  }

-- Right-hand side basic rules of inference
theorem pr { Γ : ctx } { p : form } : (Γ ∪ p) ⊢ₛ₅ p := 
  ax $ by constructor

theorem pr1 { Γ : ctx } { p q : form } : ((Γ ∪ p) ∪ q) ⊢ₛ₅ p := 
  ax $ by (repeat constructor)

theorem pr2 { Γ : ctx } { p q : form } : ((Γ ∪ p) ∪ q) ⊢ₛ₅ q := 
  ax $ by constructor

theorem by_mp1 { Γ : ctx } { p q : form } : ((Γ ∪ p) ∪ p → q) ⊢ₛ₅ q := mp pr2 pr1
theorem by_mp2 { Γ : ctx } { p q : form } : ((Γ ∪ p → q) ∪ p) ⊢ₛ₅ q := mp pr1 pr2 

theorem cut { Γ : ctx } { p q r : form } : (Γ ⊢ₛ₅ p → q) → (Γ ⊢ₛ₅ q → r) → (Γ ⊢ₛ₅ p → r) := by 
  intro hpq hqr 
  apply mp (mp pl2 (mp pl1 hqr)) hpq

theorem conv_deduction { Γ : ctx } { p q : form } : (Γ ⊢ₛ₅ p → q) → ((Γ ∪ p) ⊢ₛ₅ q) := by 
  intro hpq
  apply mp (weak hpq) pr 


-- Left-hand side basic rules of inference
theorem mp_in_ctx_left { Γ : ctx } { p q r : form } : (((Γ ∪ p) ∪ q) ⊢ₛ₅ r) → (((Γ ∪ p) ∪ p → q) ⊢ₛ₅ r) := sorry
theorem mp_in_ctx_right { Γ : ctx } { p q r : form } : (((Γ ∪ p) ∪ p → q) ⊢ₛ₅ r) → (((Γ ∪ p) ∪ q) ⊢ₛ₅ r) := sorry 


-- Basic lemmas
theorem contrap { Γ : ctx } { p q : form } : Γ ⊢ₛ₅ ((¬q) → (¬p)) → (p → q) :=
  deduction (deduction (mp (mp pl3 pr1) (mp pl1 pr2) ))
  
theorem not_impl { Γ : ctx } { p q : form } : Γ ⊢ₛ₅ (p → q) → ((¬q) → (¬p)) := sorry

theorem dne { Γ : ctx } { p : form } : Γ ⊢ₛ₅ (¬¬p) → p := 
  have h : Γ ⊢ₛ₅ (¬¬p) → ((¬p) → (¬p)) := mp pl1 idd
  mp (mp pl2 (cut pl1 pl3)) h

theorem dni { Γ : ctx } { p : form } : Γ ⊢ₛ₅ p → (¬¬p) := mp contrap dne

theorem lem { Γ : ctx } { p : form } : Γ ⊢ₛ₅ (p ∨ (¬p)) := mp dni dni

theorem not_impl_to_and { Γ : ctx } { p q : form } : Γ ⊢ₛ₅ (¬(p → q)) → (p ∨ (¬q)) := by 
  sorry

theorem and_not_to_not_impl { Γ : ctx } { p q : form } : Γ ⊢ₛ₅ (p ∧ (¬q)) → (¬(p → q)) := by
  sorry
  -- repeat (apply deduction)
  -- apply mp
  -- {
  --   apply pr1
  -- }
  -- { apply cut;
  --   { apply pr2 }
  --   { apply dni } 
  -- }

theorem box_contrap { p q : form } : ⊢ₛ₅ (□(p → q)) → (□((¬q) → (¬p))) := 
  mp k (prf.nec not_impl)

theorem diamond_k { p q : form } : ⊢ₛ₅ (□(p → q)) → ((⋄p) → (⋄q)) := 
  deduction $ mp not_impl (mp k (mp (weak box_contrap) pr))

theorem box_dne { p : form } : ⊢ₛ₅ (□(¬¬p)) → (□p) := mp k (nec dne)
theorem box_dni { p : form } : ⊢ₛ₅ (□p) → (□(¬¬p)) := mp k (nec dni)

theorem not_box_dni { p : form } : ⊢ₛ₅ (¬□p) → (¬□(¬¬p)) := mp not_impl box_dne 
theorem not_box_dne { p : form } : ⊢ₛ₅ (¬□(¬¬p)) → (¬□p) := mp not_impl box_dni 

theorem diamond_dne { p : form } : ⊢ₛ₅ (⋄(¬¬p)) → (⋄p) := not_box_dne
theorem diamond_dni { p : form } : ⊢ₛ₅ (⋄p) → (⋄(¬¬p)) := not_box_dni

theorem contrap_b { p : form } : ⊢ₛ₅ (⋄(□p)) → p := sorry

-- Notable introduction rules
theorem negintro { Γ : ctx } { p q : form } : (Γ ⊢ₛ₅ p → q) → (Γ ⊢ₛ₅ p → (¬q)) → (Γ ⊢ₛ₅ (¬p)) := sorry 
-- theorem ex_falso { Γ : ctx } { p : form } : (Γ ⊢ₛ₅ ⊥) → (Γ ⊢ₛ₅ p) := sorry
theorem ex_falso_and { Γ : ctx } { p q : form } : Γ ⊢ₛ₅ (¬p) → (p → q) := sorry 
theorem ex_falso_pos { Γ : ctx } { p q : form } : Γ ⊢ₛ₅ p → ((¬p) → q) := sorry
theorem contr_conseq { Γ : ctx } { p r : form } : Γ ⊢ₛ₅ (p → r) → (((¬p) → r) → r) := sorry
theorem impl_weak { Γ : ctx } { p q r : form } (h : ((Γ ∪ r) ⊢ₛ₅ p) → (Γ ⊢ₛ₅ p)) :
  ((Γ ⊢ₛ₅ p) → (Γ ⊢ₛ₅ q)) → (((Γ ∪ r) ⊢ₛ₅ p) → ((Γ ∪ r) ⊢ₛ₅ q)) := sorry 

theorem and_intro { Γ : ctx } { p q : form } : (Γ ⊢ₛ₅ p) → (Γ ⊢ₛ₅ q) → (Γ ⊢ₛ₅ (p ∧ q)) := sorry 
theorem and_elim_left { Γ : ctx } { p q : form } : ((Γ ∪ (p ∧ q)) ⊢ₛ₅ p) := sorry
theorem and_elim_right { Γ : ctx } { p q : form } : ((Γ ∪ (p ∧ q)) ⊢ₛ₅ q) := sorry 

theorem or_intro_left { Γ : ctx } { p q r : form } : (Γ ⊢ₛ₅ p) → (Γ ⊢ₛ₅ (p ∨ q)) := sorry 
theorem or_intro_right { Γ : ctx } { p q r : form } : (Γ ⊢ₛ₅ q) → (Γ ⊢ₛ₅ (p ∨ q)) := sorry 
theorem or_elim { Γ : ctx } { p q r : form } : (Γ ⊢ₛ₅ (p ∨ q)) → (Γ ⊢ₛ₅ p → r) → (Γ ⊢ₛ₅ q → r) → (Γ ⊢ₛ₅ r) := sorry 
theorem detach_pos { Γ : ctx } { p q : form } : ((Γ ∪ p) ⊢ₛ₅ q) → ((Γ ∪ ¬p) ⊢ₛ₅ q) → (Γ ⊢ₛ₅ q) := sorry 
theorem detach_neg { Γ : ctx } { p q : form } : ((Γ ∪ ¬p) ⊢ₛ₅ q) → ((Γ ∪ p) ⊢ₛ₅ q) → (Γ ⊢ₛ₅ q) := sorry 
