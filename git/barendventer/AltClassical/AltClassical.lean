namespace AltClassical

universe u
def CNot (ω p: Type u) := p → ω
def CPos (ω p: Type u) := CNot ω (CNot ω p)
def CImpl (ω p q: Type u) := CNot ω (CPos ω p × CNot ω q)
def COr (ω p q: Type u) := CNot ω (CNot ω p × CNot ω q)
def CAnd (ω p q: Type u) := CNot ω (COr ω (CNot ω p) (CNot ω q))
def CIff (ω p q: Type u) := COr ω (CAnd ω p q) (CAnd ω (CNot ω p) (CNot ω q))
section evaluation

def CNot.annihilate: {ω p: Type u} → CNot ω p → p → ω := λ{_ _} f x => f x
-- def CPos.annihilate: {ω p: Type u} → CPos ω p → CNot ω p → ω := CNot.annihilate
def CPos.valueOf: {p: Type u} → (∀ω, CPos ω p) → p := λ{p} nnp => nnp p id

end evaluation

section via_goal

def CNot.explosively: {p ω: Type u} → ω → CNot ω p := λ {_ _} x => λ _ => x
def CPos.explosively: {p ω: Type u} → ω → CPos ω p := CNot.explosively
def COr.explosively: {p q ω: Type u} → ω → COr ω p q := λ {_ _ _} r _ => r
def CImpl.explosively: {p q ω: Type u} → ω → CImpl ω p q := COr.explosively
def CAnd.explosively: {p q ω: Type u} → ω → CAnd ω p q := CNot.explosively
def CNot.not_false: {ω: Type u} → CNot ω ω := id

end via_goal

section liftings

def CPos.lift: {p ω: Type u} → p → CPos ω p := λx f => f x
def CNot.lift: {p ω: Type u} → (p → ω) → CNot ω p := id
def CImpl.lift: {p q ω: Type u} → (p → q) → CImpl ω p q := by
  intro p q ω f
  intro ⟨cp, cq⟩
  have ncq := CNot.lift (cq ∘ f)
  exact cp ncq

def COr.lift: {p q ω: Type u} → (p ⊕ q) → COr ω p q := by
  intro p q  ω porq ⟨np, nq⟩
  cases porq
  . exact np ‹p›
  . exact nq ‹q›
end liftings

section simplifications

def CNot.isCPos: {p ω: Type u} → (CNot ω (CNot ω p)) → CPos ω p := id 
def CPos.isCNot: {p ω: Type u} → CPos ω (CNot ω p) → CNot ω p := by
  intro p ω not_not_not_p pp
  have not_not_p: CNot ω (CNot ω p) := CPos.lift pp
  exact not_not_not_p not_not_p

def CPos.isCOr: {p q ω: Type u} → CPos ω (COr ω p q) → COr ω p q := CPos.isCNot
def CPos.isCAnd: {p q ω: Type u} → CPos ω (CAnd ω p q) → CAnd ω p q := CPos.isCNot
def CPos.isCIff: {p q ω: Type u} → CPos ω (CIff ω p q) → CIff ω p q := CPos.isCNot

def CPos.join: {p ω: Type u} → CPos ω (CPos ω p) → CPos ω p := CPos.isCNot

end simplifications



section or

def COr.elim: {p q ω: Type u} → COr ω p q → CNot ω p → CNot ω q → ω :=
  λ {_ _ _} porq np nq => porq ⟨np, nq⟩
def COr.elimLeft: {p q ω: Type u} → COr ω p q → CNot ω p → CPos ω q := COr.elim
def COr.elimRight: {p q ω: Type u} → COr ω p q → CNot ω q → CPos ω p := 
  λ{_ _ _} porq => flip (COr.elimLeft porq)
def COr.xmiddle: {p ω: Type u} → COr ω p (CNot ω p) := λ {_ _} ⟨f, g⟩ => g f
def COr.inl: {p q ω: Type u} → CPos ω p → COr ω p q := 
  λ {_ _ _} g ⟨f, _⟩ => g f
def COr.inr: {p q ω: Type u} → CPos ω q → COr ω p q := 
  λ {_ _ _} g ⟨_, f⟩ => g f
  -- intro p q ω c_porq ⟨not_p, not_q⟩
  -- apply c_porq
  -- intro porq
  -- exact COr.elim porq not_p not_q

end or

section and

def CAnd.intro: {p q ω: Type u} → CPos ω p → CPos ω q → CAnd ω p q := by
  intro p q ω cp cq not_p_or_not_q
  exact COr.elim not_p_or_not_q cp cq
def CAnd.left: {p q ω: Type u} → CAnd ω p q → CPos ω p := by
  intro p q ω p_and_q not_p
  apply p_and_q
  intro ⟨cp, _⟩
  exact cp.annihilate not_p
def CAnd.right: {p q ω: Type u} → CAnd ω p q → CPos ω q := by
  intro p q ω p_and_q not_q
  apply p_and_q
  intro ⟨_, cq⟩
  exact cq.annihilate not_q
def CAnd.lift: {p q ω: Type u} → (p × q) → CAnd ω p q := by
  intro p q ω ⟨pp, pq⟩ 
  intro not_p_or_not_q
  apply COr.elim not_p_or_not_q
  . exact (CNot.annihilate · pp)
  . exact (CNot.annihilate · pq)
def CAnd.symm: {p q ω: Type u} → CAnd ω p q → CAnd ω q p := by
  intro p q ω p_and_q
  apply CAnd.intro
  . exact (CAnd.right p_and_q)
  . exact (CAnd.left p_and_q)
def CAnd.refl: {p ω: Type u} → CPos ω p → CAnd ω p p := λcp => CAnd.intro cp cp


end and

section impl

def CImpl.elim: {p q ω: Type u} → CImpl ω p q → CPos ω p → CNot ω q → ω := COr.elim

def CImpl.mp: {p q ω: Type u} → CImpl ω p q → CPos ω p → CPos ω q := CImpl.elim

def CImpl.mt: {p q ω: Type u} → CImpl ω p q → CNot ω q → CNot ω p := 
  λ ptoq not_q pp => ptoq ⟨CPos.lift pp, not_q⟩

def CImpl.contrapositive: {p q ω: Type u} → CImpl ω p q → CImpl ω (CNot ω q) (CNot ω p)
  := by
  intro p q ω ptoq ⟨cnot_q, cpp⟩
  apply CImpl.elim ptoq
  . intro not_p
    exact cpp.annihilate not_p
  . intro pq
    have not_q: CNot ω q := CPos.isCNot cnot_q
    exact CNot.annihilate not_q pq

def CImpl.byProveConsequent: {p q ω: Type u} → CPos ω q → CImpl ω p q := COr.inr

def CImpl.byRefuteAntecedent: {p q ω: Type u} → CNot ω p → CImpl ω p q :=
  λf ⟨g, _⟩ => g f

def CImpl.pierce: {p q ω: Type u} → CImpl ω (CImpl ω (CImpl ω p q) p) p := by
  intro p q ω ⟨cf, not_p⟩
  have f := CPos.isCNot cf
  apply CImpl.elim f
  . intro not_ptoq
    have ptoq: CImpl ω p q := CImpl.byRefuteAntecedent not_p
    exact CNot.annihilate not_ptoq ptoq
  . intro pp
    exact CNot.annihilate not_p pp

def CImpl.refl: {p ω: Type u} → CImpl ω p p := CImpl.lift id
def CImpl.rfl: {p ω: Type u} → CImpl ω p p := CImpl.refl

def CImpl.trans: {p q r ω: Type u} → CImpl ω p q → CImpl ω q r → CImpl ω p r := by
  intro p q r ω p2q q2r ⟨cp, not_r⟩
  apply CImpl.elim p2q
  . intro not_p
    exact cp.annihilate not_p
  . intro pq
    apply CImpl.elim q2r
    . intro not_q
      exact CNot.annihilate not_q pq
    . intro pr
      exact CNot.annihilate not_r pr

def CPos.isCImpl: {p q ω: Type u} → CPos ω (CImpl ω p q) → CImpl ω p q := CPos.isCNot

end impl

section iff

def CIff.intro: {p q ω: Type u} → CImpl ω p q → CImpl ω q p → CIff ω p q := by
  intro p q ω p2q q2p ⟨not_p_and_q, not_not_p_and_not_q⟩
  apply CImpl.elim p2q
  . intro not_p
    apply CImpl.elim q2p
    . intro not_q
      have not_p_and_not_q: CAnd ω (CNot ω p) (CNot ω q) := CAnd.lift ⟨not_p, not_q⟩
      exact CNot.annihilate not_not_p_and_not_q not_p_and_not_q
    . intro pp
      exact CNot.annihilate not_p pp
  . intro pq
    apply CImpl.elim q2p
    . intro not_q
      exact CNot.annihilate not_q pq
    . intro pp
      exact CNot.annihilate not_p_and_q (CAnd.lift ⟨pp, pq⟩)

def CIff.mp: {p q ω: Type u} → CIff ω p q → CImpl ω p q := by
  intro p q ω p_iff_q ⟨pp, not_q⟩
  apply p_iff_q
  constructor
  . intro p_and_q
    exact p_and_q.right.annihilate not_q
  . intro notp_and_notq
    exact notp_and_notq.left.annihilate pp

def CIff.mpr: {p q ω: Type u} → CIff ω p q → CImpl ω q p := by
  intro p q ω p_iff_q ⟨pq, not_p⟩
  apply p_iff_q
  constructor
  . intro p_and_q
    exact p_and_q.left.annihilate not_p
  . intro notp_and_notq
    exact notp_and_notq.right.annihilate pq

def CIff.comm: {p q ω: Type u} → CIff ω p q → CIff ω q p := by
  intro p q ω p_iff_q ⟨ not_q_and_p, not_notq_and_notp ⟩
  apply p_iff_q
  constructor
  . intro p_and_q
    apply not_q_and_p
    apply CAnd.symm
    assumption
  . intro notp_and_notq
    apply not_notq_and_notp
    apply CAnd.symm
    assumption
def CIff.symm: {p q ω: Type u} → CIff ω p q → CIff ω q p := CIff.comm
--TODO: Can this be implemented?
--def CIff.subst: {p q ω: Type u} → {f: Type u → Type u} → CIff ω p q → f p → f q
def CIff.rfl: {p ω: Type u} → CIff ω p p := CIff.intro CImpl.refl CImpl.refl
def CIff.trans: {p q r ω: Type u} → CIff ω p q → CIff ω q r → CIff ω p r := by
  intro p q r ω p_iff_q q_iff_r ⟨ not_p_and_r, not_notp_and_notr ⟩
  apply p_iff_q
  constructor
  . intro p_and_q
    apply q_iff_r
    constructor
    . intro q_and_r
      exact CNot.annihilate not_p_and_r (CAnd.intro (CAnd.left p_and_q) (CAnd.right q_and_r))
    . intro notq_and_notr
      exact CNot.annihilate (CAnd.left notq_and_notr) (CAnd.right p_and_q)
  . intro notp_and_notq
    apply q_iff_r
    constructor
    . intro q_and_r
      exact CNot.annihilate (CAnd.right notp_and_notq) (CAnd.left q_and_r)
    . intro notq_and_notr
      exact CNot.annihilate not_notp_and_notr (CAnd.intro (CAnd.left notp_and_notq) (CAnd.right notq_and_notr))
def CIff.fromAnd: {p q ω: Type u} → CAnd ω p q → CIff ω p q := by
  intro p q ω p_and_q ⟨not_p_and_q, _⟩
  exact CNot.annihilate not_p_and_q p_and_q

end iff

section demorgans

def CAnd.refuteCases: {p q ω: Type u} → CAnd ω p q → CNot ω (COr ω (CNot ω p) (CNot ω q)) := id

def CNot.distribute_and: 
  {p q ω: Type u} → CNot ω (CAnd ω p q) → COr ω (CNot ω p) (CNot ω q) := CPos.isCNot

def CAnd.factor_not:
  {p q ω: Type u} → CAnd ω (CNot ω p) (CNot ω q) → CNot ω (COr ω p q) := by
    intro p q ω not_p_and_not_q p_or_q
    apply not_p_and_not_q
    intro ⟨not_not_not_p, not_not_not_q⟩
    apply COr.elim p_or_q
    . exact CPos.isCNot not_not_not_p
    . exact CPos.isCNot not_not_not_q

def CNot.distribute_or:
  {p q ω: Type u} → CNot ω (COr ω p q) → CAnd ω (CNot ω p) (CNot ω q) := by
    intro p q ω not_porq
    apply CAnd.intro
    . intro cp
      exact CNot.annihilate not_porq (COr.inl cp)
    . intro cq
      exact CNot.annihilate not_porq (COr.inr cq)

def COr.factor_not:
  {p q ω: Type u} → COr ω (CNot ω p) (CNot ω q) → CNot ω (CAnd ω p q) := by
    intro p q ω notp_or_notq p_and_q
    apply COr.elim notp_or_notq
    . exact p_and_q.left.annihilate
    . exact p_and_q.right.annihilate

def CIff.demorgans_not_and:
  {p q ω: Type u} → CIff ω (CNot ω (CAnd ω p q)) (COr ω (CNot ω p) (CNot ω q)) 
    := CIff.intro (CImpl.lift CNot.distribute_and) (CImpl.lift COr.factor_not)

def CIff.demorgans_not_or:
  {p q ω: Type u} → CIff ω (CNot ω (COr ω p q)) (CAnd ω (CNot ω p) (CNot ω q))
    := CIff.intro (CImpl.lift CNot.distribute_or) (CImpl.lift CAnd.factor_not)
    
end demorgans
end AltClassical