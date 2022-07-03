import AltClassical

-- https://mathweb.ucsd.edu/~jeggers/math109/tautologies.pdf

section a_list_of_tautologies
open AltClassical
universe u
variable (p q r s ω: Type u)

-- 1. p ∨ ¬p
example: COr ω p (CNot ω p) := by
  intro ⟨not_p, not_not_p⟩
  exact CNot.annihilate not_not_p not_p

-- 2. ¬(p ∧ ¬p)
example: CNot ω (CAnd ω p (CNot ω p)) := by
  intro p_and_not_p
  apply p_and_not_p
  intro ⟨cp, not_cp⟩
  exact CNot.annihilate not_cp cp

-- 3. p → p
example: CImpl ω p p := CImpl.lift id

section idempotent_laws

-- 4.a. p ↔ (p ∨ p)
example: CIff ω p (COr ω p p) := by
  apply CIff.intro
  . intro ⟨cp, not_p_or_p⟩
    have p_or_p: COr ω p p := COr.inl cp
    exact CNot.annihilate not_p_or_p p_or_p
  . intro ⟨c_p_or_p, not_p⟩
    have p_or_p: COr ω p p := CPos.isCNot c_p_or_p
    exact COr.elim p_or_p not_p not_p

-- 4.b. p ↔ (p ∧ p)
example: CIff ω p (CAnd ω p p) := by
  apply CIff.intro
  . intro ⟨cp, not_p_and_p⟩
    have p_and_p: CAnd ω p p := CAnd.intro cp cp
    exact CNot.annihilate not_p_and_p p_and_p
  . intro ⟨c_p_and_p, not_p⟩
    apply c_p_and_p
    intro p_and_p
    exact CNot.annihilate (CAnd.left p_and_p) not_p

end idempotent_laws

-- double negation
-- 5. p ↔ ¬¬p
example: CIff ω p ((CNot ω (CNot ω p))) := by
  apply CIff.intro
  . intro ⟨cp, not_cp⟩
    exact CNot.annihilate not_cp cp
  . intro ⟨cnnp, np⟩
    have nnp := CPos.isCNot cnnp
    exact CNot.annihilate nnp np

section commutative_laws
-- 6.a. (p ∨ q) ↔ (q ∨ p)
example: CIff ω (COr ω p q) (COr ω q p) := by
  apply CIff.intro
  . intro ⟨cporq, not_qorp⟩
    apply cporq
    intro porq
    apply COr.elim porq
    . intro pp
      exact CNot.annihilate not_qorp (COr.inr (CPos.lift pp))
    . intro pq
      exact CNot.annihilate not_qorp (COr.inl (CPos.lift pq))
  . intro ⟨cqorp, not_porq⟩
    apply COr.elim (CPos.isCOr cqorp)
    . intro pq
      exact CNot.annihilate not_porq (COr.inr (CPos.lift pq))
    . intro pp
      exact CNot.annihilate not_porq (COr.inl (CPos.lift pp))

-- 6.b. (p ∧ q) ↔ (q ∧ p)
example: CIff ω (CAnd ω p q) (CAnd ω q p) := by
  apply CIff.intro
  . intro ⟨cpandq, not_qandp⟩
    apply cpandq
    intro pandq
    exact CNot.annihilate not_qandp (CAnd.intro (CAnd.right pandq) (CAnd.left pandq))
  . intro ⟨cqandp, not_pandq⟩
    apply cqandp
    intro qandp
    exact CNot.annihilate not_pandq (CAnd.intro (CAnd.right qandp) (CAnd.left qandp))

-- 6.c. (p ↔ q) ↔ (q ↔ p)
example: CIff ω (CIff ω p q) (CIff ω q p) := by
  apply CIff.intro
  . intro ⟨cpiffq, not_qiffp⟩
    apply cpiffq
    intro piffq
    have qiffp := CIff.intro (CIff.mpr piffq) (CIff.mp piffq)
    exact CNot.annihilate not_qiffp qiffp
  . intro ⟨cqiffp, not_piffq⟩
    apply cqiffp
    intro qiffp
    apply not_piffq
    exact CIff.intro (CIff.mpr qiffp) (CIff.mp qiffp)

end commutative_laws

section associative_laws

-- 7.a. (p ∨ (q ∨ r)) ↔ ((p ∨ q) ∨ r)
example: CIff ω (COr ω p (COr ω q r)) (COr ω (COr ω p q) r) := by
  apply CIff.intro
  . intro ⟨c_p_orqr, not_pq_orr⟩
    apply c_p_orqr
    intro p_orqr
    apply COr.elim p_orqr
    . intro pp
      apply not_pq_orr
      intro ⟨not_porq, _⟩
      apply not_porq
      intro ⟨not_p, _⟩
      exact CNot.annihilate not_p pp
    . intro qorr
      apply qorr.elim
      . intro pq
        apply not_pq_orr
        intro ⟨not_porq, _⟩
        apply not_porq
        intro ⟨_, not_q⟩
        exact CNot.annihilate not_q pq
      . intro pr
        apply not_pq_orr
        intro ⟨_, not_r⟩
        exact CNot.annihilate not_r pr
  . intro ⟨c_pq_orr, not_p_orqr⟩
    apply c_pq_orr
    intro pq_orr
    apply COr.elim pq_orr
    . intro porq
      apply not_p_orqr
      intro ⟨not_p, not_qorr⟩
      apply not_qorr
      intro ⟨not_q, _⟩
      apply COr.elim porq
      . exact not_p
      . exact not_q
    . intro pr
      apply not_p_orqr
      intro ⟨_, not_qorr⟩
      exact CNot.annihilate not_qorr (COr.inr (CPos.lift pr))

-- 7.b. (p ∧ (q ∧ r)) ↔ ((p ∧ r) ∧ q)
example: CIff ω (CAnd ω p (CAnd ω q r)) (CAnd ω (CAnd ω p q) r) := by
  apply CIff.intro
  . intro ⟨c_p_qandr, not_pandq_r⟩
    apply not_pandq_r
    intro not_pandq_or_r
    apply not_pandq_or_r
    constructor
    . intro not_pandq
      apply not_pandq
      intro notp_or_notq
      apply notp_or_notq
      constructor
      . exact c_p_qandr.isCAnd.left.annihilate
      . exact c_p_qandr.isCAnd.right.isCAnd.left.annihilate
    . intro not_r
      exact c_p_qandr.isCAnd.right.isCAnd.right.annihilate not_r
  . intro ⟨c_p_qandr, not_p_qandr⟩
    apply c_p_qandr
    intro pandq_r
    apply not_p_qandr
    intro notp_or_notqandr
    apply notp_or_notqandr
    constructor
    . intro not_p
      exact pandq_r.left.isCAnd.left.annihilate not_p
    . intro not_qandr
      apply not_qandr
      intro notq_or_notr
      apply notq_or_notr
      constructor
      . intro not_q
        exact pandq_r.left.isCAnd.right.annihilate not_q
      . intro not_r
        exact pandq_r.right.annihilate not_r

end associative_laws

section distributive_laws

-- 8.a (p ∧ (q ∨ r)) ↔ ((p ∧ q) ∨ (p ∧ r))
example: CIff ω (CAnd ω p (COr ω q r)) (COr ω (CAnd ω p q) (CAnd ω p r)) := by
  apply CIff.intro
  . intro ⟨c_pandqorr, not_pandq_or_pandr⟩
    apply not_pandq_or_pandr
    intro ⟨not_pandq, not_pandr⟩
    have cp := c_pandqorr.isCAnd.left
    apply c_pandqorr
    intro pandqorr
    apply pandqorr.right.isCOr.elim
    . intro pq
      have pandq := CAnd.intro cp (CPos.lift pq)
      exact not_pandq pandq
    . intro pr
      have pandr := CAnd.intro cp (CPos.lift pr)
      exact not_pandr.annihilate pandr
  . intro ⟨c_pandq_or_pandr, not_pandqorr⟩
    apply not_pandqorr
    intro notp_or_not_qorr
    apply notp_or_not_qorr
    constructor
    . intro not_p
      apply c_pandq_or_pandr.isCOr.elim
      . intro pandq
        exact pandq.left.annihilate not_p
      . intro pandr
        exact pandr.left.annihilate not_p
    . intro not_qorr
      apply not_qorr
      intro ⟨not_q, not_r⟩
      apply c_pandq_or_pandr.isCOr
      constructor
      . intro p_and_q
        exact p_and_q.right.annihilate not_q
      . intro p_and_r
        exact p_and_r.right.annihilate not_r


-- 8.b. (p ∨ (q ∧ r)) ↔ ((p ∨ q) ∧ (p ∨ r))
example: CIff ω (COr ω p (CAnd ω q r)) (CAnd ω (COr ω p q) (COr ω p r)) := by
  apply CIff.intro
  . intro ⟨cporqandr, not_porqandporr⟩
    apply cporqandr
    intro p_or_qandr
    apply not_porqandporr
    intro porq_and_porr
    apply porq_and_porr.elim
    . intro not_porq
      apply not_porq
      intro ⟨not_p, not_q⟩
      have qandr := p_or_qandr.elimLeft not_p
      exact qandr.isCAnd.left.annihilate not_q
    . intro not_porr
      apply not_porr
      intro ⟨not_p, not_r⟩
      have qandr := p_or_qandr.elimLeft not_p
      exact qandr.isCAnd.right.annihilate not_r
  . intro ⟨c_porq_and_porr, not_p_or_qandr⟩
    apply c_porq_and_porr
    intro porq_and_porr
    apply not_p_or_qandr
    intro ⟨not_p, not_qandr⟩
    apply not_qandr
    intro notq_or_notr
    apply porq_and_porr
    intro ⟨cporq, cporr⟩
    apply cporq
    intro porq
    apply cporr
    intro porr
    apply COr.elim notq_or_notr
    . intro not_q 
      have cp := porq.elimRight not_q
      exact cp.annihilate not_p
    . intro not_r
      have cp := porr.elimRight not_r
      exact cp.annihilate not_p

end distributive_laws

section identity_laws

-- 9.a. p ∨ C ↔ p
example: CIff ω (COr ω p ω) p := by
  apply CIff.intro
  . intro ⟨c_porfalse, not_p⟩
    apply c_porfalse.isCOr.elimLeft not_p
    exact CNot.not_false
  . intro ⟨cp, not_porfalse⟩
    apply not_porfalse
    intro ⟨not_p, _⟩
    exact cp.annihilate not_p

-- 9.b. p ∧ C ↔ C
example: CIff ω (CAnd ω p ω) ω := by
  apply CIff.intro
  . intro ⟨cpandfalse, _⟩
    apply cpandfalse.isCAnd.right
    exact CNot.not_false
  . intro ⟨cfalse, _⟩
    apply cfalse
    exact CNot.not_false

-- 9.c. p ∨ T ↔ T
example: CIff ω (COr ω p (CNot ω ω)) (CNot ω ω) := by
  apply CIff.intro
  . intro ⟨_, not_true⟩
    apply not_true
    exact CNot.not_false
  . intro ⟨_, not_p_or_true⟩
    apply not_p_or_true
    intro ⟨_, not_true⟩
    apply not_true
    exact CNot.not_false

-- 9.d. p ∧ T ↔ T
example: CIff ω (CAnd ω p (CNot ω ω)) p := by
  apply CIff.intro
  . intro ⟨cp_and_true, not_p⟩
    apply cp_and_true
    intro p_and_true
    exact p_and_true.left.annihilate not_p
  . intro ⟨cp, not_pandtrue⟩
    exact not_pandtrue.annihilate (CAnd.intro cp (CPos.lift CNot.not_false))

end identity_laws

section demorgan's_laws

-- 10.a. ¬(p ∧ q) ↔ ¬p ∨ ¬q
example: CIff ω (CNot ω (CAnd ω p q)) (COr ω (CNot ω p) (CNot ω q)) := by
  apply CIff.intro
  . intro ⟨not_pandq, not_notp_or_notq⟩
    apply not_notp_or_notq
    intro ⟨cp, cq⟩
    exact not_pandq.isCNot.annihilate (CAnd.intro cp cq)
  . intro ⟨c_notp_or_notq, c_pandq⟩
    apply c_pandq
    intro pandq
    apply c_notp_or_notq.isCOr.elim
    . exact pandq.left
    . exact pandq.right

-- 10.b. ¬(p ∨ q) ↔ ¬p ∧ ¬q
example: CIff ω (CNot ω (COr ω p q)) (CAnd ω (CNot ω p) (CNot ω q)) := by
  apply CIff.intro
  . intro ⟨not_porq, not_notp_and_notq⟩
    apply not_porq.isCNot
    intro not_p_times_not_q
    exact not_notp_and_notq (CAnd.lift not_p_times_not_q)
  . intro ⟨not_p_and_not_q, c_p_or_q⟩
    apply c_p_or_q
    intro porq
    apply porq.elim
    . exact not_p_and_not_q.isCAnd.left.isCNot
    . exact not_p_and_not_q.isCAnd.right.isCNot

end demorgan's_laws

section equivalence

--11.a. (p ↔ q) ↔ ((p → q) ∧ (q → p))
example: CIff ω (CIff ω p q) (CAnd ω (CImpl ω p q) (CImpl ω q p)) := by
  apply CIff.intro
  . intro ⟨cpiffq, np2qandq2p⟩
    apply np2qandq2p
    intro np2qornq2p
    apply np2qornq2p.elim
    . apply CPos.lift
      exact cpiffq.isCIff.mp
    . apply CPos.lift
      exact cpiffq.isCIff.mpr
  . intro ⟨p2qandq2p, npiffq⟩
    apply npiffq
    apply CIff.intro
    . exact p2qandq2p.isCAnd.left.isCImpl
    . exact p2qandq2p.isCAnd.right.isCImpl

--11.b. (p ↔ q) ↔ ((p ∧ q) ∨ (¬p ∧ ¬q))
example: CIff ω (CIff ω p q) (COr ω (CAnd ω p q) (CAnd ω (CNot ω p) (CNot ω q))) := by
  apply CIff.intro
  . intro ⟨cpiffq, not_pandqornotpandnotq⟩
    apply not_pandqornotpandnotq
    exact cpiffq.isCIff
  . intro ⟨c_pandqornotpandnotq, not_piffq⟩
    apply c_pandqornotpandnotq.isCOr.elim
    . intro pandq
      apply not_piffq
      intro ⟨not_pandq, _⟩
      exact not_pandq.annihilate pandq
    . intro not_p_and_not_q
      apply not_piffq
      intro ⟨_, not_notpandnotq⟩
      exact not_notpandnotq.annihilate not_p_and_not_q

--11.c. (p ↔ q) ↔ (¬p ↔ ¬q)
example: CIff ω (CIff ω p q) (CIff ω (CNot ω p) (CNot ω q)) := by
  apply CIff.intro
  . intro ⟨cpiffq, not_notpiffnotq⟩
    apply cpiffq
    intro piffq
    have np2nq := piffq.mpr.contrapositive
    have nq2np := piffq.mp.contrapositive
    apply not_notpiffnotq
    apply CIff.intro
    . exact np2nq
    . exact nq2np
  . intro ⟨cnotpiffnotq, notpiffq⟩
    apply cnotpiffnotq.isCIff
    constructor
    . intro notp_and_notq
      apply notpiffq
      intro ⟨_, not_notp_and_notq⟩
      exact not_notp_and_notq notp_and_notq
    . intro cp_and_cq
      apply cp_and_cq
      intro ⟨(cp: CPos ω (CPos ω p)), (cq: CPos ω (CPos ω q))⟩
      apply notpiffq
      intro ⟨not_pandq, _⟩
      apply not_pandq
      apply CAnd.intro
      . exact cp.join
      . exact cq.join

end equivalence

section implication
--12.a. (p → q) ↔ (¬q → ¬p)
example: CIff ω (CImpl ω p q) (CImpl ω (CNot ω q) (CNot ω p)) := by
  apply CIff.intro
  . intro ⟨cp2q, nnq2np⟩
    apply nnq2np
    intro ⟨cnq, cp⟩
    apply cp2q.isCImpl.elim
    . exact cp
    . exact cnq.isCNot
  . intro ⟨nq2np, np2q⟩
    apply np2q
    intro ⟨cp, nq⟩
    apply nq2np.isCImpl.elim
    . apply CPos.lift
      exact nq
    . exact cp

--12.b. ¬(p → q) ↔ (p ∧ ¬q)
example: CIff ω (CNot ω (CImpl ω p q)) (CAnd ω p (CNot ω q)) := by
  apply CIff.intro
  . intro ⟨cnotp2q, not_pandnotq⟩
    have notp2q := cnotp2q.isCNot
    apply notp2q
    intro ⟨cp, nq⟩
    apply not_pandnotq
    apply CAnd.intro
    . exact cp
    . exact CPos.lift nq
  . intro ⟨cpandnotq, cp2q⟩
    have p2q := cp2q.isCPos.isCImpl
    have pandnq2false := cpandnotq.isCAnd
    apply pandnq2false
    intro ⟨cp, ncq⟩
    apply ncq
    intro nq
    apply p2q.elim
    . exact cp
    . exact nq

end implication

-- contrapositive
--13. (p → q) ↔ (¬q → ¬p)
example: CIff ω (CImpl ω p q) (CImpl ω (CNot ω q) (CNot ω p)) := by
  apply CIff.intro
  . intro ⟨cp2q, not_nq2np⟩
    apply cp2q.isCImpl.elim
    . intro not_p
      have nq2np: CImpl ω (CNot ω q) _ := CImpl.byProveConsequent (CPos.lift not_p)
      exact not_nq2np.annihilate nq2np
    . intro pq
      have nq2np: CImpl ω _ (CNot ω p) := CImpl.byRefuteAntecedent (CPos.lift pq)
      exact not_nq2np.annihilate nq2np
  . intro ⟨nq2np, not_p2q⟩
    apply nq2np.isCImpl.elim
    . intro cq
      have p2q: CImpl ω p q := CImpl.byProveConsequent cq
      exact not_p2q.annihilate p2q
    . intro not_p
      have p2q: CImpl ω p q := CImpl.byRefuteAntecedent not_p
      exact not_p2q.annihilate p2q

-- reductio ad absurdum
--14. (p → q) ↔ ((p ∧ ¬q) → C)
example: CIff ω (CImpl ω p q) (CImpl ω (CAnd ω p (CNot ω q)) ω) := by
  apply CIff.intro
  . intro ⟨cp2q, not_absurd⟩
    apply not_absurd
    intro ⟨cpandnotq, _⟩
    apply cp2q.isCImpl.elim
    . intro not_p
      exact cpandnotq.isCAnd.left.annihilate not_p
    . intro pq
      exact cpandnotq.isCAnd.right.annihilate (CPos.lift pq)
  . intro ⟨c_absurd, not_p2q⟩
    apply not_p2q
    intro ⟨cp, not_q⟩
    apply c_absurd.isCImpl.mp
    . apply CPos.lift
      intro notp_orq
      apply notp_orq.elim
      . exact cp
      . exact CPos.lift not_q
    . exact CNot.not_false

--15.a. ((p → r) ∧ (q → r)) ↔ ((p ∨ q) → r)
example: CIff ω (CAnd ω (CImpl ω p r) (CImpl ω q r)) (CImpl ω (COr ω p q) r) := by
  apply CIff.intro
  . intro ⟨p2randq2r, not_porq2r⟩
    apply not_porq2r
    intro ⟨cporq, not_r⟩
    apply cporq.isCOr.elim
    . intro pp
      have cr: CPos ω r := p2randq2r.isCAnd.left.isCImpl.mp (CPos.lift pp)
      exact cr.annihilate not_r
    . intro pq
      have cr: CPos ω r := p2randq2r.isCAnd.right.isCImpl.mp (CPos.lift pq)
      exact cr.annihilate not_r
  . intro ⟨cporq2r, not_p2randq2r⟩
    apply cporq2r.isCImpl.elim
    . apply CPos.lift
      intro ⟨not_p, not_q⟩
      apply not_p2randq2r
      intro notp2r_or_notq2r
      apply notp2r_or_notq2r.elim
      . apply CPos.lift
        intro ⟨cp, _⟩
        exact cp.annihilate not_p
      . apply CPos.lift
        intro ⟨cq, _⟩
        exact cq.annihilate not_q
    . intro pr
      have p2r: CImpl ω p r := CImpl.byProveConsequent (CPos.lift pr)
      have q2r: CImpl ω q r := CImpl.byProveConsequent (CPos.lift pr)
      apply not_p2randq2r
      apply CAnd.intro
      . exact CPos.lift p2r
      . exact CPos.lift q2r

--15.b. ((p → q) ∧ (p → r)) ↔ (p → (q ∧ r))
example: CIff ω (CAnd ω (CImpl ω p q) (CImpl ω p r)) (CImpl ω p (CAnd ω q r)) := by
  apply CIff.intro
  . intro ⟨p2qandq2r, not_p_to_qandr⟩
    apply not_p_to_qandr
    intro ⟨cp, not_qandr⟩
    apply not_qandr
    apply CAnd.intro
    . intro not_q
      have cq: CPos ω q := p2qandq2r.isCAnd.left.isCImpl.mp cp
      exact cq.annihilate not_q
    . intro not_r
      have cr: CPos ω r := p2qandq2r.isCAnd.right.isCImpl.mp cp
      exact cr.annihilate not_r
  . intro ⟨cp_to_qandr, not_p2randq2r⟩
    apply not_p2randq2r
    apply CAnd.intro
    . apply CPos.lift
      intro ⟨cp, not_q⟩
      have qandr := cp_to_qandr.isCImpl.mp cp
      exact qandr.isCAnd.left.annihilate not_q
    . apply CPos.lift
      intro ⟨cp, not_r⟩
      have qandr := cp_to_qandr.isCImpl.mp cp
      exact qandr.isCAnd.right.annihilate not_r

--15.c. ((p → q) ∨ (p → r)) ↔ (p → (q ∨ r))
example: CIff ω (COr ω (CImpl ω p q) (CImpl ω p r)) (CImpl ω p (COr ω q r)) := by
  apply CIff.intro
  . intro ⟨c_p2q_or_p2r, not_p2qorr⟩
    apply not_p2qorr
    intro ⟨cp, not_qorr⟩
    apply c_p2q_or_p2r.isCImpl.elim
    . intro not_pandnotq
      apply not_pandnotq
      apply Prod.mk
      . exact cp
      . intro pq
        exact not_qorr.annihilate (COr.inl (CPos.lift pq))
    . intro p2r
      have cr := p2r.mp cp
      exact not_qorr (COr.inr cr)
  . intro ⟨p_to_qorr, not_p2q_or_p2r ⟩
    apply not_p2q_or_p2r
    intro ⟨not_p2q, not_p2r⟩
    apply p_to_qorr.isCImpl.elim
    . intro not_p
      exact not_p2q (CImpl.byRefuteAntecedent not_p)
    . intro qorr
      apply qorr.elim
      . intro pq
        exact not_p2q (CImpl.byProveConsequent (CPos.lift pq))
      . intro pr
        exact not_p2r (CImpl.byProveConsequent (CPos.lift pr))

-- exportation law
--16. ((p ∧ q) → r) ↔ (p → (q → r))
example: CIff ω (CImpl ω (CAnd ω p q) r) (CImpl ω p (CImpl ω q r)) := by
  apply CIff.intro
  . intro ⟨pandq_to_r, not_p_to_q2r⟩
    apply not_p_to_q2r
    intro ⟨cp, not_q2r⟩
    have q2r: CImpl ω q r := by
      intro ⟨cq, not_r⟩
      have cr := pandq_to_r.isCImpl.mp (CPos.lift (CAnd.intro cp cq))
      exact cr.annihilate not_r
    exact not_q2r.annihilate q2r
  . intro ⟨p_to_q2r, not_pandq_to_r⟩
    apply not_pandq_to_r
    intro ⟨cpandq, not_r⟩
    have q2r := p_to_q2r.isCImpl.mp (cpandq.isCAnd.left)
    have cr := q2r.isCImpl.mp (cpandq.isCAnd.right)
    exact cr.annihilate not_r

-- addition
--17. p → (p ∨ q)
example: CImpl ω p (COr ω p q) := by
  intro ⟨cp, not_porq⟩
  exact not_porq.annihilate (COr.inl cp)

-- simplification
-- 18. (p ∧ q) → p
example: CImpl ω (CAnd ω p q) p := by
  intro ⟨pandq, not_p⟩
  exact pandq.isCAnd.left.annihilate not_p

-- modus ponens
-- 19. (p ∧ (p → q)) → q
example: CImpl ω (CAnd ω p (CImpl ω p q)) q := by
  intro ⟨pandp2q, not_q⟩
  have cp := pandp2q.isCAnd.left
  have p2q := pandp2q.isCAnd.right.isCImpl
  apply p2q.elim
  . exact cp
  . exact not_q

-- modus tollens
-- 20. ((p → q) ∧ ¬q) → ¬p
example: CImpl ω (CAnd ω (CImpl ω p q) (CNot ω q)) (CNot ω p) := by
  intro ⟨p2q_and_notq, cp⟩
  have p2q := p2q_and_notq.isCAnd.left.isCImpl
  have not_q := p2q_and_notq.isCAnd.right.isCNot
  apply p2q.elim
  . exact cp
  . exact not_q

-- hypothetical syllogism, aka transitivity
-- 21. ((p → q) ∧ (q → r)) → (p → r)
example: CImpl ω (CAnd ω (CImpl ω p q) (CImpl ω q r)) (CImpl ω p r) := by
  intro ⟨p2q_and_q2r, not_p2r⟩
  apply not_p2r
  intro ⟨cp, not_r⟩
  apply p2q_and_q2r.isCAnd.right.isCImpl.elim
  . intro not_q
    apply p2q_and_q2r.isCAnd.left.isCImpl.elim
    . exact cp
    . exact not_q
  . exact not_r

-- disjunctive syllogism
-- 22. ((p ∨ q) ∧ ¬p) → q
example: CImpl ω (CAnd ω (COr ω p q) (CNot ω p)) q := by
  intro ⟨porq_and_notp, not_q⟩
  have porq := porq_and_notp.isCAnd.left.isCOr
  have not_p := porq_and_notp.isCAnd.right.isCNot
  apply porq.elim
  . exact not_p
  . exact not_q

-- absurdity
-- 23. (p → C) → ¬p
example: CImpl ω (CImpl ω p ω) (CNot ω p) := by
  intro ⟨absurd_p, cp⟩
  have absurd := absurd_p.isCImpl
  have falsity := absurd.mp cp.isCPos
  apply falsity
  exact CNot.not_false

-- 24. ((p → q) ∧ (r → s)) → ((p ∨ r) → (q ∨ s))
example: CImpl ω (CAnd ω (CImpl ω p q) (CImpl ω r s)) (CImpl ω (COr ω p r) (COr ω q s)) := by
  intro ⟨f_and_g, xory_to_worz⟩
  have f := f_and_g.isCAnd.left.isCImpl
  have g := f_and_g.isCAnd.right.isCImpl
  apply xory_to_worz
  intro ⟨xory, not_worz⟩
  apply xory.isCOr.elim
  . intro px
    exact not_worz.annihilate (COr.inl (f.mp (CPos.lift px)))
  . intro py
    exact not_worz.annihilate (COr.inr (g.mp (CPos.lift py)))

-- 25. (p → q) → ((p ∨ r) → (q ∨ r))
example: CImpl ω (CImpl ω p q) (CImpl ω (COr ω p r) (COr ω q r)) := by
  intro ⟨p2q, not_porr2qorr⟩
  apply not_porr2qorr
  intro ⟨cporr, not_qorr⟩
  apply not_qorr
  intro ⟨not_q, not_r⟩
  apply p2q.isCImpl.elim
  . intro not_p
    apply cporr.isCOr.elim
    . exact not_p
    . exact not_r
  . exact not_q

end a_list_of_tautologies