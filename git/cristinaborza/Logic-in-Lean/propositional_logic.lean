open Classical

variable (p q r s : Prop)

---------------------------------
-- Double negation elimination --
---------------------------------
example (h : ¬¬p) : p :=
  Or.elim (em p) 
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)


------------------
-- Modus Ponens --
------------------
example : p → (p → q) → q := 
  fun (hp : p) (hpq : p → q) => hpq hp 


----------------------
-- De Morgan's rules -
----------------------

-- ¬(p ∧ q) ↔ (¬p ∨ ¬q)
example : ¬(p ∧ q) ↔ (¬p ∨ ¬q):=
  Iff.intro
  (
    fun h : ¬(p ∧ q) =>
    Or.elim (em p)
    (
      fun hp : p =>
      Or.elim (em q) 
      (
        fun hq : q =>
        have hpq : p ∧ q := And.intro hp hq 
        show ¬p ∨ ¬q from absurd hpq h
      )
      (fun hnq : ¬q => show ¬p ∨ ¬q from Or.inr hnq) 
    )
    (fun hnp : ¬p => Or.inl hnp)
  )
  (
    fun h : ¬p ∨ ¬q =>
    Or.elim h
    (
      fun hnp : ¬p =>
      fun hpq : p ∧ q =>
      absurd (And.left hpq) hnp 
    )
    (
      fun hnq : ¬q =>
      fun hpq : p ∧ q =>
      absurd (And.right hpq) hnq
    )
  )

-- ¬(p ∨ q) ↔ (¬p ∧ ¬q)
example : ¬(p ∨ q) ↔ (¬p ∧ ¬q):=
  Iff.intro 
  (
    fun h₀ : ¬(p ∨ q) =>
    have hnp : ¬p := fun hp : p => h₀ (Or.inl hp)
    have hnq : ¬q := fun hq : q => h₀ (Or.inr hq)
    show ¬p ∧ ¬q from And.intro hnp hnq
  )
  (
    fun h₀ : ¬p ∧ ¬q =>
    fun h₁ : p ∨ q =>
    Or.elim h₁ 
      (fun hp : p => absurd hp (And.left h₀))
      (fun hq : q => absurd hq (And.right h₀))
  )


------------------------------
-- Commutativity of ∧ and ∨ --
------------------------------

-- Commutativity of ∧
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
  (
    fun hpq : p ∧ q =>
    show q ∧ p from And.intro (And.right hpq) (And.left hpq)
  )
  (
    fun hqp : q ∧ p =>
    show p ∧ q from And.intro (And.right hqp) (And.left hqp)
  )
  
  
-- Commutativity of ∨ 
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
  (
    fun hpq : p ∨ q =>
    Or.elim hpq (fun hp => Or.inr hp) (fun hq => Or.inl hq)
  )
  (
    fun hqp : q ∨ p =>
    Or.elim hqp (fun hq => Or.inr hq) (fun hp => Or.inl hp)
  )


------------------------------
-- Associativity of ∧ and ∨ --
------------------------------

-- Associativity of ∧
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro
  (
    fun hpqr : (p ∧ q) ∧ r =>
    have hp : p := And.left (And.left hpqr)
    have hq : q := And.right (And.left hpqr)
    have hr : r := And.right hpqr
    show p ∧ (q ∧ r) from And.intro (And.left (And.left hpqr)) (And.intro hq hr)
  )
  (
    fun hpqr : p ∧ (q ∧ r) =>
    have hp : p := And.left hpqr
    have hq : q := And.left (And.right hpqr)
    have hr : r := And.right (And.right hpqr)
    show (p ∧ q) ∧ r from And.intro (And.intro hp hq) hr
  )


-- Associativity of ∨ 
example : (p ∨ q) ∨ r → p ∨ (q ∨ r) := 
  fun hpqr : (p ∨ q) ∨ r =>
  Or.elim hpqr
  (
    fun hpq : p ∨ q =>
    Or.elim hpq 
    (
      fun hp : p => 
      show p ∨ (q ∨ r) from Or.inl hp
    )
    (
      fun hq : q =>
      have hqr : q ∨ r := Or.inl hq
      show p ∨ (q ∨ r) from Or.inr hqr
    )
  )
  (
    fun hr : r => 
    have hqr : q ∨ r := Or.inr hr
    show p ∨ (q ∨ r) from Or.inr hqr
  )

--------------------
-- Distributivity --
--------------------
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro 
  (
    fun hpqr : p ∧ (q ∨ r) =>
    have hqr : q ∨ r := And.right hpqr
    Or.elim hqr
    (
      fun hq : q =>
      have hpq : p ∧ q := And.intro (And.left hpqr) hq 
      show (p ∧ q) ∨ (p ∧ r) from Or.inl hpq
    )
    (
      fun hr : r =>
      have hpr : p ∧ r := And.intro (And.left hpqr) hr 
      show (p ∧ q) ∨ (p ∧ r) from Or.inr hpr
    )
  )
  (
    fun h : (p ∧ q) ∨ (p ∧ r) =>
    Or.elim h 
    (
      fun hpq : p ∧ q =>
      show p ∧ (q ∨ r) from And.intro (And.left hpq) (Or.inl (And.right hpq))
    )
    (
      fun hpr : p ∧ r =>
      show p ∧ (q ∨ r) from And.intro (And.left hpr) (Or.inr (And.right hpr))
    )
  )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro 
  (
    fun hpqr : p ∨ (q ∧ r) =>
    Or.elim hpqr 
    (
      fun hp : p =>
      have hpq : p ∨ q := Or.inl hp 
      have hpr : p ∨ r := Or.inl hp
      show (p ∨ q) ∧ (p ∨ r) from And.intro hpq hpr
    )
    (
      fun hqr : q ∧ r =>
      have hpq : p ∨ q := Or.inr (And.left hqr)
      have hpr : p ∨ r := Or.inr (And.right hqr)
      show (p ∨ q) ∧ (p ∨ r) from And.intro hpq hpr
    )
  )
  (
    fun h : (p ∨ q) ∧ (p ∨ r) =>
    have hpq : p ∨ q := And.left h
    have hpr : p ∨ r := And.right h 
    Or.elim hpq
    (fun hp : p => Or.inl hp)
    (
      fun hq : q =>
      Or.elim hpr
      (fun hp : p => Or.inl hp)
      (
        fun hr : r =>
        have hqr : q ∧ r := And.intro hq hr
        show p ∨ (q ∧ r) from Or.inr hqr
      )
    )
  )


----------------------
-- Other properties --
----------------------
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro
  (
    fun hpqr : p → (q → r) =>
    fun hpq : p ∧ q =>
    have hqr : q → r := hpqr (And.left hpq)
    show r from hqr (And.right hpq)
  )
  (
    fun hpqr : p ∧ q → r =>
    fun hp : p =>
    fun hq : q =>
    have hpq : p ∧ q := And.intro hp hq 
    show r from hpqr hpq 
  )

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  Iff.intro
  (
    fun h₀ : (p ∨ q) → r =>
    have h₁ : p → r := fun hp : p => h₀ (Or.inl hp)
    have h₂ : q → r := fun hq : q => h₀ (Or.inr hq)
    show (p → r) ∧ (q → r) from And.intro h₁ h₂
  )
  (
    fun h₀ : (p → r) ∧ (q → r) => 
    fun h₁ : p ∨ q =>
    Or.elim h₁ 
      (fun hp : p => (And.left h₀) hp)
      (fun hq : q => (And.right h₀) hq)
  )

example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬p => absurd (And.left h) (And.right h)

example : p ∧ ¬q → ¬(p → q) := 
  fun h₀ : p ∧ ¬q =>
  fun h₁ : p → q =>
  absurd (h₁ (And.left h₀)) (And.right h₀)

example : ¬p → (p → q) := 
  fun h₀ : ¬p =>  
  fun h₁ : p =>
  show q from absurd h₁ h₀ 

example : (¬p ∨ q) → (p → q) :=
  fun h₀ : ¬p ∨ q =>
  fun h₁ : p =>
  Or.elim h₀ 
    (fun h₂ : ¬p => show q from absurd h₁ h₂)
    (fun h₂ : q => show q from h₂)

example : p ∨ False ↔ p := 
  Iff.intro
  (
    fun h₀ : p ∨ False =>
    Or.elim h₀ 
      (fun hp : p => hp)
      (fun h₁ : False => show p from False.elim h₁)
  )
  (
    fun hp : p =>
    show p ∨ False from Or.inl hp
  )

example : p ∧ False ↔ False := 
  Iff.intro
  (
    fun h₀ : p ∧ False =>
    show False from And.right h₀
  )
  (
    fun h₀ : False =>
    show p ∧ False from False.elim h₀
  )


example : (p → q) → (¬q → ¬p) :=
  fun h₀ : p → q =>
  fun h₁ : ¬q =>
  fun h₂ : p =>
  absurd (h₀ h₂) h₁ 


example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
  fun h₀ : p → r ∨ s =>
  Or.elim (em p)
  (
    fun hp : p =>
    have hrs : r ∨ s := h₀ hp 
    Or.elim hrs 
    (
      fun hr : r =>
      have hpr : p → r := fun _ : p => hr
      show (p → r) ∨ (p → s) from Or.inl hpr
    )
    (
      fun hs : s =>
      have hps : p → s := fun _ : p => hs
      show (p → r) ∨ (p → s) from Or.inr hps
    )
  )
  (
    fun hnp : ¬p =>
    have hpr : p → r :=  fun hp : p => absurd hp hnp     
    show (p → r) ∨ (p → s) from Or.inl hpr
  )

example : ¬(p → q) → p ∧ ¬q := 
  fun h₀ : ¬(p → q) => 
  Or.elim (em q) 
  (
    fun hq : q =>
    have hpq : p → q := fun _ : p => hq 
    show p ∧ ¬q from absurd hpq h₀
  )
  (
    fun hnq : ¬q =>
    Or.elim (em p)
    (
      fun hp : p =>
      show p ∧ ¬q from And.intro hp hnq
    )
    (
      fun hnp : ¬p =>
      have hpq : p → q := fun hp : p => absurd hp hnp 
      show p ∧ ¬q from absurd hpq h₀
    )
  )
