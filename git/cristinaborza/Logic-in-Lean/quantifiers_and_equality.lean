--------------------------------
-- *Quantifiers and Equality* --
--------------------------------

------------------------------
-- The Universal Quantifier --
------------------------------
variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd 

universe u

-- Equality --
#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
example (a : α) (b : α) : (a, b).1 = a := rfl
example : 2 + 3 = 5 := rfl

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

#check @congrArg
#check @congrFun
#check @congr

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
  

variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  by simp [h1, h2, h3, Nat.add_comm, h4]

-- Calculational Proofs --
#check @Nat.succ_le_succ

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  := by rw [Nat.mul_add]
        _ = x * x + y * x + (x + y) * y            := by rw [Nat.add_mul]
        _ = x * x + y * x + (x * y + y * y)        := by rw [Nat.add_mul]
        _ = x * x + y * x + x * y + y * y          := by rw [←Nat.add_assoc]

-- ← rewrite in the opposite direction
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw[Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

-- The Existential Quantifier --
#check @Nat.zero_lt_succ
#check @Exists.intro

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h 

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

/- We can use the anonymous constructor notation *⟨t, h⟩* for 
Exists.intro t h, when the type is clear from the context. -/

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩ 

example (x : Nat) (h : x > 0) : ∃ y, y < x := ⟨0, h⟩  

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z := 
  ⟨y, hxy, hyz⟩ 


/- Note that Exists.intro has implicit arguments: Lean has to infer the 
predicate p : α → Prop in the conclusion ∃ x, p x. This is not a trivial affair. 
For example, if we have have hg : g 0 0 = 0 and write Exists.intro 0 hg, 
there are many possible values for the predicate p, corresponding to the 
theorems ∃ x, g x x = x, ∃ x, g x x = 0, ∃ x, g x 0 = x, etc. 
Lean uses the context to infer which one is appropriate. This is illustrated 
in the following example, in which we set the option pp.explicit to true to 
ask Lean's pretty-printer to show the implicit arguments.-/

variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

/-
We can view Exists.intro as an information-hiding operation, since it hides the 
witness to the body of the assertion. The existential elimination rule, 
*Exists.elim*, performs the opposite operation. It allows us to prove a 
proposition q from ∃ x : α, p x, by showing that q follows from p w for an 
arbitrary value w. Roughly speaking, since we know there is an x satisfying p x,
we can give it a name, say, w. If q does not mention w, then showing that q 
follows from p w is tantamount to showing the q follows from the existence 
of any such x. Here is an example: 
-/

variable (α : Type) (p q : α → Prop)

#check @Exists.elim
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := 
  Exists.elim h 
  (
    fun w =>
    fun hw : p w ∧ q w =>
    show ∃ x, q x ∧ p x from Exists.intro w (And.intro hw.right hw.left)
  )

/- 
It may be helpful to compare the exists-elimination rule to the or-elimination 
rule: the assertion ∃ x : α, p x can be thought of as a big disjunction of the 
propositions p a, as a ranges over all the elements of α. Note that the anonymous 
constructor notation *⟨w, hw.right, hw.left⟩* abbreviates a nested constructor 
application; we could equally well have written *⟨w, ⟨hw.right, hw.left⟩⟩*.
-/

/- 
Lean provides a more convenient way to eliminate from an existential quantifier 
with the *match expression*:
-/

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := 
  match h with 
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩ 

-- We can annotate the types used in the match for greater clarity: 
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := 
  match h with 
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩ 

-- We can even use the match statement to decompose the conjunction at the same time:
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := 
  match h with 
  | ⟨w, hwl, hwr⟩ => ⟨w, hwr, hwl⟩ 

-- Lean also provides a pattern-matching let expression:
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x := 
  let ⟨w, hwl, hwr⟩ := h 
  ⟨w, hwr, hwl⟩

/- This is essentially just alternative notation for the match construct above. 
Lean will even allow us to use an implicit match in the fun expression: -/
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

/- In the following example, we define even a as ∃ b, a = 2 * b, and then we 
show that the sum of two even numbers is an even number. -/

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 
  (
    fun w1 => 
    fun hw1 : a = 2 * w1 =>
    Exists.elim h2 
    (
      fun w2 =>
      fun hw2 : b = 2 * w2 =>
      Exists.intro (w1 + w2)
      (
        calc 
          a + b = 2 * w1 + 2 * w2 := by rw[hw1, hw2]
          _ = 2 * (w1 + w2) := by rw[Nat.mul_add]
      )
    )
  )

/- 
Using the various gadgets described in this chapter --- 
*the match statement*, *anonymous constructors*, and the *rewrite tactic*, 
we can write this proof concisely as follows:
-/

theorem even_plus_even' (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with 
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw[hw1, hw2, Nat.mul_add]⟩

/-
Just as the constructive "or" is stronger than the classical "or," so, too, is the 
constructive "exists" stronger than the classical "exists". For example, the following 
implication requires classical reasoning because, from a constructive standpoint, 
knowing that it is not the case that every x satisfies ¬ p is not the same as having
a particular x that satisfies p -/

open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
  (
    fun h1 : ¬ ∃ x, p x =>
    have h2 : ∀ x, ¬ p x :=
      fun x =>
      fun h3 : p x =>
      have h4 : ∃ x, p x :=  ⟨x, h3⟩
      show False from h1 h4
    show False from h h2)

/-
What follows are some common identities involving the existential quantifier. 
In the exercises below, we encourage you to prove as many as you can. We also leave it 
to you to determine which are nonconstructive, and hence require some form of 
classical reasoning.-/

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := fun ⟨x, r⟩ => r  
example (a : α) : r → (∃ x : α, r) := fun pr : r => ⟨a, pr⟩ 
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  Iff.intro
  (fun ⟨x, pxr⟩ => ⟨⟨x, And.left pxr⟩, And.right pxr⟩)
  (
    fun h₀ : (∃ x, p x) ∧ r =>
    match And.left h₀ with 
    | ⟨x, px⟩ => Exists.intro x (And.intro px (And.right h₀))
  )

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  Iff.intro
  (
    fun ⟨x, hpq⟩ =>
    Or.elim hpq
      (fun hp : p x => Or.inl (Exists.intro x hp))
      (fun hq : q x => Or.inr (Exists.intro x hq))
  )
  (
    fun h₀ : (∃ x, p x) ∨ (∃ x, q x) =>
    Or.elim h₀ 
      (fun ⟨x, px⟩ => ⟨x, Or.inl px⟩)
      (fun ⟨x, qx⟩ => ⟨x, Or.inr qx⟩)
  )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from  hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))


-- theorem dne {p : Prop} (h : ¬¬p) : p :=
--   Or.elim (em p) 
--     (fun hp : p => hp)
--     (fun hnp : ¬p => absurd hnp h)


theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p) 
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  Iff.intro
  (
    fun ⟨x, h₀⟩ =>
    byContradiction
    (
      fun h₁ : ¬ ¬ ∀ x, ¬ p x =>
      have h₂ : ∀ x, ¬ p x := dne h₁
      show False from absurd h₀ (h₂ x)
    )
  )
  (
    fun h₀ : ¬ (∀ x, ¬ p x) =>
    byContradiction
    (
      fun h₁ : ¬ ∃ x, p x =>
      have h₂ : ∀ x, ¬ p x :=
        fun x =>
        fun h₃ : p x =>
        have h₄ : ∃ x, p x := ⟨x, h₃⟩ 
        show False from h₁ h₄
      show False from h₀ h₂
    )
  )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
