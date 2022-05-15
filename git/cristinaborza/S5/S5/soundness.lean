import S5.syntax.lemmas
import S5.semantics.lemmas

theorem soundness { Γ : ctx } { p : form } : (Γ ⊢ₛ₅ p) → (Γ ⊩ₛ₅ p) := by 
  intro h 
  induction h 
  {
    apply sem_csq.is_true;
    intros; 
    apply ctx_tt_to_mem_tt;
    repeat assumption
  }
  {
    apply sem_csq.is_true;
    intros;
    apply is_true_pl1;
    repeat assumption
  }
  {
    apply sem_csq.is_true;
    intros;
    apply is_true_pl2;
    repeat assumption
  }
  {
    apply sem_csq.is_true;
    intros;
    apply is_true_pl3;
    repeat assumption 
  }
  {
    sorry
    -- cazul mp
  }
  {
    apply sem_csq.is_true;
    intros;
    apply is_true_k;
    repeat assumption 
  }
  {
    apply sem_csq.is_true;
    intros;
    apply is_true_t;
    repeat assumption
  }
  {
    apply sem_csq.is_true;
    intros;
    apply is_true_s4;
    repeat assumption
  }
  {
    sorry
    -- trebuie scris is_true_s5
  }
  {
    apply sem_csq.is_true;
    intros;
    sorry;
    sorry
  }