theorem forall_to_exists (p : Store → Heap → Heap → Prop) (f : ¬ ∀ s h h', ¬ (p s h h') ) : ∃ s h h', (p s h h') :=
  Classical.byContradiction
    (fun hyp1 : ¬ ∃ s h h', p s h h' =>
      have hyp2 : ∀ s h h', ¬ p s h h' :=
        fun s h h' =>
        fun hyp3 : p s h h' =>
        have hyp4 : ∃ s h h', p s h h' := ⟨ s , ⟨ h , ⟨h', hyp3⟩ ⟩ ⟩
        show False from hyp1 hyp4
      show False from f hyp2)

def dne {p} (hyp : ¬¬p) : p :=
  Classical.byContradiction
    (fun hyp1 : ¬p =>
     show False from hyp hyp1)

def dni {P : Prop} : P → ¬¬P := by {
  intros p np;
  exact np p;
}

theorem dne_equivalence {p}: ¬¬p ↔ p := by
  apply Iff.intro
  case mp =>  intro nnp; exact (dne nnp)
  case mpr => intro p; exact (dni p)

theorem dna_equivalence {p}: p ↔ ¬¬p:= by
  apply Iff.intro
  case mp => intro p; exact (dni p)
  case mpr =>  intro nnp; exact (dne nnp)


theorem exists_n_implies_n_forall {p : α → Prop} : (∃ x , ¬ p x) → (¬ ∀ x , p x) := by
  intro ⟨ x, not_p_x ⟩
  intro for_all
  have p_x := for_all x
  exact not_p_x p_x

theorem exists_implies_n_forall_n {p : α → Prop} : (∃ x , p x) → (¬ ∀ x , ¬ p x) := by
  intro ⟨ x, p_x ⟩
  intro for_all
  have not_p_x := for_all x
  exact not_p_x p_x

theorem forall_implies_n_exists_n {p : α → Prop} : (∀ x , p x) → ¬(∃ x , ¬ p x) := by
  intro for_all
  intro ⟨ x, not_p_x ⟩
  have p_x := for_all x
  exact not_p_x p_x

theorem forall_n_implies_n_exists {p : α → Prop} : (∀ x , ¬ p x) → ¬(∃ x , p x) := by
  intro for_all
  intro ⟨ x, p_x ⟩
  have not_p_x := for_all x
  exact not_p_x p_x

theorem contrapos {A B : Prop} : (A → B) → ((¬B) → (¬A)) := by {
  intro a_to_b not_b a;
  exact not_b (a_to_b a);
}

theorem inverse {A B : Prop} : ((¬B) → (¬A)) → (A → B) := by {
  intro nb_to_na;
  intro a;
  apply Classical.byContradiction;
  apply @contrapos (¬B) (¬A) nb_to_na;
  apply dni;
  exact a;
}

theorem pp_imp_nn {A B : Prop} : (A → B) ↔ ((¬B) → (¬A)) := by
  apply Iff.intro
  case mp  => apply contrapos
  case mpr => apply inverse

theorem np_imp_pn {A B : Prop} : ((¬A) → B) ↔ ((¬B) → A) := by
  apply Iff.intro
  case mp  =>
    conv =>
      lhs
      rw [pp_imp_nn]
    intro nb_to_nna
    intro not_b
    have nna := nb_to_nna not_b
    exact (dne nna)
  case mpr =>
    intro nb_to_a
    intro not_a
    apply Classical.byContradiction (
      λ not_b => by
      have a := nb_to_a not_b
      exact not_a a
    )

theorem pn_imp_np {A B : Prop} : (A → (¬B)) ↔ (B → (¬A)) := by
  apply Iff.intro
  case mp  =>
    conv =>
      lhs
      rw [pp_imp_nn]
    intro nnb_to_na
    intro b
    have nnb := (dni b)
    exact nnb_to_na nnb
  case mpr =>
    intro b_to_na
    intro a
    apply Classical.byContradiction (
      λ nnb => by
      have not_a := b_to_na (dne nnb)
      exact not_a a
    )


theorem n_imp {P Q : Prop} : ((¬ P) → Q) ↔ (P ∨ Q) := by
  apply Iff.intro
  case mp  =>
    intro not_p_imp_q
    have p_or_not_p := Classical.em P
    apply Or.elim p_or_not_p
      (
        λ p => Or.inl p
      )
      (
        λ np => Or.inr (not_p_imp_q np)
      )
  case mpr =>
    intro p_or_q
    cases p_or_q with
    | inl p =>
      intro np
      apply absurd p np
    | inr q => intro; exact q

theorem n_forall_implies_exists_n {p : α → Prop} : ¬(∀ x , p x) → (∃ x , ¬ p x) := by {
  rw [np_imp_pn];
  intro not_exists x;
  cases Classical.em (p x) with
  | inl p_x => exact p_x;
  | inr np_x => {
    apply False.elim;
    apply not_exists;
    apply Exists.intro x;
    exact np_x
  }
}

theorem exists_same_as_forall {p : α → Prop} : (∃ x , ¬ p x) ↔ (¬ ∀ x , p x) := by
  apply Iff.intro
  case mp  => apply exists_n_implies_n_forall
  case mpr => apply n_forall_implies_exists_n

theorem not_imp {A B : Prop} : ¬ (A → B) ↔ A ∧ ¬ B := by
  apply Iff.intro
  case mp  => {
    rw [np_imp_pn];
    rw [n_imp];
    cases Classical.em A with
    | inl a => {
      cases Classical.em B with
      | inl b => apply (Or.intro_right (A ∧ ¬B) (λ _ => b));
      | inr nb => apply (Or.intro_left (A → B) (And.intro a nb));
    }
    | inr na => {
      cases Classical.em B with
      | inl b => apply (Or.intro_right (A ∧ ¬B) (λ _ => b));
      | inr nb => apply (Or.intro_right (A ∧ ¬B) (λ a => absurd a na));
    }
  }
  case mpr => {
    rw [pn_imp_np];
    intro a_imp_b;
    intro a_and_nb;
    have a := a_and_nb.left;
    have nb := a_and_nb.right;
    exact (nb (a_imp_b a));
  }

variable
  {α β γ: Type}
  (x : α)
  (y : β)
  (z : γ)
  (p : α → β → γ → Prop)
  (t : α × β × γ)

def p3 : α × β × γ :=
  (x, y, z)

def p3_app : Prop := p (t.fst) (t.snd.fst) (t.snd.snd)

theorem p3_app_id : p3_app p (p3 x y z) ↔ p x y z := Iff.intro id id

theorem fa3 : (∀ x y z , p x y z) ↔ (∀ t , (p3_app p) t) := by {
  apply Iff.intro;
  case mp  => {
    intro sep;
    intro t;
    have x := t.fst;
    have y := t.snd.fst;
    have z := t.snd.snd;
    simp [p3_app]
    apply sep;
  }
  case mpr => {
    intro comb;
    intro x y z;
    rw [← (p3_app_id x y z p)];
    exact comb (p3 x y z);
  }
}

theorem e3 : (∃ x y z , ¬ p x y z) ↔ (∃ t , ¬ (p3_app p) t) := by {
  apply Iff.intro;
  case mp  => {
    intro ⟨ x , ⟨ y , ⟨ z , not_p ⟩⟩⟩;
    have t := p3 x y z;
    apply Exists.intro (p3 x y z);
    apply not_p;
  }
  case mpr => {
    intro ⟨ t, not_t ⟩;
    apply Exists.intro t.fst;
    apply Exists.intro t.snd.fst;
    apply Exists.intro t.snd.snd;
    apply not_t;
  }
}


theorem exists_same_as_forall_3 : ¬(∀ x y z , p x y z) ↔ (∃ x y z , ¬ p x y z) := by {
  rw [(fa3 p)];
  rw [(e3 p)];
  apply (Iff.symm exists_same_as_forall);
}



