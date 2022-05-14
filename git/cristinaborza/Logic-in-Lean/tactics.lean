---------------
-- *Tactics* --
---------------

--------------------------
-- Entering Tactic Mode --
--------------------------

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by 
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

/- The *apply tactic* applies an expression, viewed as denoting a function with 
zero or more arguments. It unifies the conclusion with the expression in the 
current goal, and creates new goals for the remaining arguments, provided that 
no later arguments depend on them. In the example above, the command 
*apply And.intro* yields two subgoals: 

    case left
    p : Prop,
    q : Prop,
    hp : p,
    hq : q
    ⊢ p

    case right
    p : Prop,
    q : Prop,
    hp : p,
    hq : q
    ⊢ q ∧ p

-/

/- The first goal is met with the command *exact hp*. The exact command is just a 
variant of apply which signals that the expression given should fill the goal
exactly. It is good form to use it in a tactic proof, since its failure signals 
that something has gone wrong. It is also more robust than apply, since the 
elaborator takes the expected type, given by the target of the goal, into 
account when processing the expression that is being applied. In this case, 
however, apply would work just as well.-/

/- You can see the resulting proof term with the *#print* command:-/

#print test

/- Tactic commands can take compound expressions, not just single identifiers. 
The following is a shorter version of the preceding proof: -/

theorem test' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

/- Tactics that may produce multiple subgoals often tag them. For example, the 
tactic apply And.intro tagged the first sugoal as left, and the second as right. 
In the case of the apply tactic, the tags are inferred from the parameters 
names used in the And.intro declaration. You can structure your tactics using 
the notation case <tag> => <tactics>. The following is a structured version of 
our first tactic proof in this chapter. -/

theorem test'' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

/- For simple sugoals, it may not be worth selecting a subgoal using its tag, but you may still
 want to structure the proof. Lean also provides the "bullet" notation 
 . <tactics> (or · <tactics>) for structuring proof. -/

theorem test''' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

-------------------
-- Basic Tactics --
-------------------

/- In addition to apply and exact, another useful tactic is *intro*, which 
introduces a hypothesis. What follows is an example of an identity from 
propositional logic that we proved in a previous chapter, now proved using 
tactics. -/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

/- The intro command can more generally be used to introduce a variable of any type: -/

example (α : Type) : α → α := by 
  intro a 
  exact a

example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact rfl

/- You can use it to introduce several variables: -/

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂ 
  exact Eq.trans (Eq.symm h₂) h₁

/- As the apply tactic is a command for constructing function applications
interactively, the intro tactic is a command for constructing function 
abstractions interactively (i.e., terms of the form fun x => e). As with 
lambda abstraction notation, the intro tactic allows us to use an implicit match.-/

example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩


/- You can also provide multiple alternatives like in the match expression.-/
example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by 
  intro 
  | ⟨w, hpw, hqw⟩ => exact ⟨w, hqw, hpw⟩

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
    | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
    | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

/- The *assumption* tactic looks through the assumptions in context of the 
current goal, and if there is one matching the conclusion, it applies it. -/

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  apply Eq.trans h₃
  exact rfl

/- The following example uses the intros command to introduce the three 
variables and two hypotheses automatically: -/

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

/- The rfl tactic is syntax sugar for exact rfl -/
example (y : Nat) : (fun x : Nat => 0) y = 0 :=
  by rfl

/- The repeat combinator can be used to apply a tactic several times. -/
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  repeat assumption

/- Another tactic that is sometimes useful is the *revert* tactic, 
which is, in a sense, an inverse to intro.-/

example (x : Nat) : x = x := by
  revert x -- goal is ⊢ ∀ (x : Nat), x = x
  intro y -- goal is y : Nat ⊢ y = y
  rfl

example (x : Nat) : x = x := by rfl

/- Moving a hypothesis into the goal yields an implication: -/
example (x y : Nat) (h : x = y) : y = x := by
  apply Eq.symm h 

example (x y : Nat) (h : x = y) : y = x := by
  revert h 
  intro h₁ 
  apply Eq.symm 
  assumption

/- But revert is even more clever, in that it will revert not only an element of 
the context but also all the subsequent elements of the context that depend on it. 
For example, reverting x in the example above brings h along with it: -/

example (x y : Nat) (h : x = y) : y = x := by
  revert x -- goal is y : Nat ⊢ ∀ (x : Nat), x = y → y = x
  intros
  apply Eq.symm
  assumption

/- The mnemonic in the notation above is that you are generalizing the goal by 
setting 3 to an arbitrary variable x. Be careful: not every generalization 
preserves the validity of the goal. Here, *generalize* replaces a goal that could 
be proved using rfl with one that is not provable:-/

example : 2 + 3 = 5 := by rfl

example : 2 + 3 = 5 := by
  generalize  3 = x -- goal is x : Nat ⊢ 2 + x = 5
  admit

/- In this example, the admit tactic is the analogue of the sorry proof term. 
It closes the current goal, producing the usual warning that sorry has been used.
To preserve the validity of the previous goal, the generalize tactic allows us 
to record the fact that 3 has been replaced by x. All you need to do is to 
provide a label, and generalize uses it to store the assignment in the local 
context:-/

example : 2 + 3 = 5 := by
  generalize h : 3 = x -- goal is x : Nat, h : 3 = x ⊢ 2 + x = 5
  rw [← h]

--------------------
-- *More Tactics* --
--------------------

/- Some additional tactics are useful for constructing and destructing propositions 
and data. For example, when applied to a goal of the form p ∨ q, you use tactics 
such as apply Or.inl and apply Or.inr. Conversely, the cases tactic can be used to 
decompose a disjunction. -/

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

/- You can also use a *(unstructured)* cases without the with and a tactic for 
each alternative. -/

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption

/- The (unstructured) cases is particularly useful when you can close several 
subgoals using the same tactic. -/

-- example (p q : Prop) : p ∨ q → q ∨ p := by
--   intro h
--   cases h 
--   repeat assumption

/- The cases tactic can also be used to decompose a conjunction. -/

example (p q : Prop) : p ∧ q → q ∧ p := by
  intro h 
  cases h with 
  | intro hp hq => constructor; exact hq; exact hp 

/- You can use cases and constructor with an existential quantifier: -/

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px

/- Here, the constructor tactic leaves the first component of the existential 
assertion, the value of x, implicit. It is represented by a metavariable, which 
should be instantiated later on. In the previous example, the proper value of the
metavariable is determined by the tactic exact px, since px has type p x. If you 
want to specify a witness to the existential quantifier explicitly, you can use 
the *exists tactic* instead -/

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => exists x; apply Or.inl; exact px  

example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq => 
    cases hpq with 
    | intro hp hq => exists x; exact And.intro hq hp
  
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x
      constructor <;> assumption

/- These tactics can be used on data just as well as propositions. In the next 
two examples, they are used to define functions which swap the components of the 
product and sum types: -/

def swap_pair : α × β → β × α := by
  intro p
  cases p 
  constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
  intro p 
  cases p 
  . apply Sum.inr; assumption
  . apply Sum.inl; assumption


/- Note that up to the names we have chosen for the variables, the definitions 
are identical to the proofs of the analogous propositions for conjunction and 
disjunction. The cases tactic will also do a case distinction on a natural number: -/

open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m with 
  | zero => exact h₀
  | succ m' => exact h₁ m'

/- The *contradiction* tactic searches for a contradiction among the hypotheses of 
the current goal: -/

example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h 
  contradiction  

/- You can also use match in tactic blocks. -/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro 
  . intro
  | ⟨hp, Or.inl hq⟩ => exact Or.inl ⟨hp, hq⟩
  | ⟨hp, Or.inr hr⟩ => exact Or.inr ⟨hp, hr⟩
  . intro 
  | Or.inl ⟨hp, hq⟩ => exact ⟨hp, Or.inl hq⟩
  | Or.inr ⟨hp, hr⟩ => exact ⟨hp, Or.inr hr⟩    

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
     | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
     | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
     | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
     | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption

---------------------------------
-- *Structuring Tactic Proofs* --
---------------------------------

/- Tactics often provide an efficient way of building a proof, but long sequences 
of instructions can obscure the structure of the argument. In this section, we 
describe some means that help provide structure to a *tactic-style proof*, making 
such proofs more readable and robust. -/

/- One thing that is nice about Lean's proof-writing syntax is that it is 
possible to *mix term-style and tactic-style proofs*, and pass between the two 
freely. For example, the tactics apply and exact expect arbitrary terms, which 
you can write using have, show, and so on. Conversely, when writing an arbitrary 
Lean term, you can always invoke the tactic mode *by inserting a by block*. The 
following is a somewhat toy example: -/

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

-- The following is a more natural example:
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h.right with
    | inl hq =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inl ⟨h.left, hq⟩
    | inr hr =>
      show (p ∧ q) ∨ (p ∧ r)
      exact Or.inr ⟨h.left, hr⟩
  . intro h
    cases h with
    | inl hpq =>
      show p ∧ (q ∨ r)
      exact ⟨hpq.left, Or.inl hpq.right⟩
    | inr hpr =>
      show p ∧ (q ∨ r)
      exact ⟨hpr.left, Or.inr hpr.right⟩

/- The show tactic can actually be used to rewrite a goal to something 
definitionally equivalent: -/

example (n : Nat) : n + 1 = Nat.succ n := by rfl

example (n : Nat) : n + 1 = Nat.succ n := by 
  show Nat.succ n = Nat.succ n 
  rfl

/- There is also a *have tactic*, which introduces a new subgoal, just as when 
writing proof terms: -/

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have hpq : p ∧ q := And.intro hp hq
    apply Or.inl
    exact hpq
  | inr hr =>
    have hpr : p ∧ r := And.intro hp hr
    apply Or.inr
    exact hpr

/- As with proof terms, you can omit the label in the have tactic, in which case,
the default label this is used: -/

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  show (p ∧ q) ∨ (p ∧ r)
  cases hqr with
  | inl hq =>
    have : p ∧ q := And.intro hp hq
    apply Or.inl
    exact this
  | inr hr =>
    have : p ∧ r := And.intro hp hr
    apply Or.inr
    exact this

/- The types in a have tactic can be omitted, so you can write have 
*hp := h.left* and have *hqr := h.right*. In fact, with this notation, you can 
even omit both the type and the label, in which case the new fact is introduced 
with the label this. -/

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq =>
    have := And.intro hp hq
    apply Or.inl; exact this
  | inr hr => 
    have := And.intro hp hr 
    apply Or.inr; exact this

/- Lean also has a *let* tactic, which is similar to the *have* tactic, but is 
used to introduce local definitions instead of auxiliary facts. It is the tactic 
analogue of a let in a proof term. -/

example : ∃ x, x + 2 = 8 := by 
  let a : Nat := 6
  exists a
  rfl

/- We have used . to create nested tactic blocks. In a nested block, Lean focuses 
on the first goal, and generates an error if it has not been fully solved at the 
end of the block. This can be helpful in indicating the separate proofs of 
multiple subgoals introduced by a tactic. The notation . is whitespace sensitive 
and relies on the indentation to detect whether the tactic block ends. 
Alternatively, you can define tactic blocks usind curly braces and semicolons. -/

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }

--------------------------
-- *Tactic Combinators* --
--------------------------

/- *Tactic combinators* are operations that form new tactics from old ones. 
A sequencing combinator is already implicit in the by block: -/

example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl; assumption

/- Here, apply Or.inl; assumption is functionally *equivalent to a single tactic* 
which first applies apply Or.inl and then applies assumption.


In *t₁ <;> t₂*, the <;> operator provides a parallel version of the sequencing 
operation: *t₁ is applied to the current goal, and then t₂ is applied to all* 
the resulting subgoals:
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption

/- This is especially useful when the resulting goals can be finished off in a 
uniform way, or, at least, when it is possible to make progress on all of them 
uniformly. 
 
The *first | t₁ | t₂ | ... | tn* applies each tᵢ until one succeeds, or else fails: -/

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption 

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption 

/- In the first example, the left branch succeeds, whereas in the second one, it 
is the right one that succeeds. In the next three examples, the same compound 
tactic succeeds in each case. -/

example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
  by repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

-- *Be careful: repeat (try t) will loop forever, because the inner tactic never fails.*

/- In a proof, there are often multiple goals outstanding. Parallel sequencing is 
one way to arrange it so that a single tactic is applied to multiple goals, but 
there are other ways to do this. For example, *all_goals t* applies t to all open 
goals: -/

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

/- In this case, the *any_goals* tactic provides a more robust solution. It is 
similar to all_goals, except it fails unless its argument succeeds on at 
least one goal. -/

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  any_goals constructor
  any_goals assumption

-- The first tactic in the by block below repeatedly splits conjunctions:
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
    p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

-- In fact, we can compress the full tactic down to one line:
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
      p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))


-----------------
-- *Rewriting* --
-----------------

-- Here are some more examples with lists:
open List

example (xs : List Nat)
        : reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs := by
  simp

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp [Nat.add_comm]

example (xs ys : List α)
        : length (reverse (xs ++ ys)) = length xs + length ys := by
  simp
  apply Nat.add_comm
