import AltClassical

section ch3_examples

open AltClassical
variable (p q r s ω: Type u)

example : CImpl ω (CImpl ω p (COr ω r s)) (COr ω (CImpl ω p r) (CImpl ω p s)) := by
  apply CImpl.lift
  intro p_to_r_or_s ⟨not_p_to_r, not_p_to_s⟩
  apply CImpl.elim p_to_r_or_s
  . intro not_p
    have p_to_r: CImpl ω p r := CImpl.byRefuteAntecedent not_p
    exact CNot.annihilate not_p_to_r p_to_r
  . intro r_or_s
    apply COr.elim r_or_s
    . intro pr
      have p_to_r: CImpl ω p r := CImpl.byProveConsequent (CPos.lift pr)
      exact CNot.annihilate not_p_to_r p_to_r
    . intro ps
      have p_to_s: CImpl ω p s := CImpl.byProveConsequent (CPos.lift ps)
      exact CNot.annihilate not_p_to_s p_to_s

example : CImpl ω (CNot ω (CAnd ω p q)) (COr ω (CNot ω p) (CNot ω q)) := by
  apply CImpl.lift
  intro not_p_and_q ⟨cp, cq⟩
  exact CNot.annihilate not_p_and_q (CAnd.intro cp cq)

example : CImpl ω (CNot ω (CImpl ω p q)) (COr ω (CNot ω p) (CNot ω q)) := by
  apply CImpl.lift
  intro not_p_to_q ⟨_, cq⟩
  have p_to_q: CImpl ω p q := CImpl.byProveConsequent cq
  exact CNot.annihilate not_p_to_q p_to_q

example : CImpl ω (CNot ω (CImpl ω p q)) (CAnd ω p (CNot ω q)) := by
  apply CImpl.lift
  intro not_p_to_q
  apply CAnd.intro
  . intro not_p
    have p_to_q: CImpl ω p q := CImpl.byRefuteAntecedent not_p
    exact CNot.annihilate not_p_to_q p_to_q
  . intro cq
    have p_to_q: CImpl ω p q := CImpl.byProveConsequent cq
    exact CNot.annihilate not_p_to_q p_to_q

example : CImpl ω (CImpl ω p q) (COr ω (CNot ω p) q) := by
  apply CImpl.lift
  intro p_to_q
  intro ⟨cp, not_q⟩
  apply CImpl.elim p_to_q
  . exact cp
  . exact not_q

example : CImpl ω (CImpl ω (CNot ω q) (CNot ω p)) (CImpl ω p q) := by
  apply CImpl.lift
  intro not_q_to_not_p ⟨cp, not_q⟩
  apply CImpl.elim not_q_to_not_p
  . intro cq
    exact cq not_q
  . intro not_p
    exact cp not_p

example : COr ω p (CNot ω p) := by
  intro ⟨not_p, not_not_p⟩
  exact not_not_p not_p

example : CImpl ω (CImpl ω (CImpl ω p q) p) p := by
  intro ⟨g, not_p⟩
  have g' : CImpl ω (CImpl ω p q) p := CPos.isCNot g
  apply CImpl.elim g'
  . intro not_p_to_q
    have p_to_q: CImpl ω p q := CImpl.byRefuteAntecedent not_p
    exact CNot.annihilate not_p_to_q p_to_q
  . intro pp
    exact CNot.annihilate not_p pp

example : CImpl ω (CNot ω (CNot ω p)) (CPos ω p) := CImpl.lift id

end ch3_examples