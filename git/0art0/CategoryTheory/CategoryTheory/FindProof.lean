import Lean
import Lean.Elab
import Lean.Elab.Tactic
import Lean.Meta
open Lean Expr Elab Meta Tactic

set_option pp.proofs true
set_option pp.proofs.withType true

/-
If the expression is of the form
A₁ → A₂ → A₃ → … → Aₙ → … → B,
the output of `targetType` is the type of `B`.

Essentially, it recovers the type of the term at the end of a series of nested implications.
-/
def getTargetType (e : Expr) : MetaM Expr :=
  Meta.forallTelescope e (λ _ t => pure t)

/-
This is the backbone of the `findProof` tactic, which is meant to find proofs (or equivalently, construct terms) of propositions (or types) involving only implications (or function arrows).

It works by first introducing all the necessary hypotheses, and then scanning the local context for terms having the goal as the "target type" (see above for the definition of a target type).

Once such a term is found, the tactic tries to recursively construct terms required to "unlock" the target, i.e., if `f : A₁ → A₂ → … → Aₙ → … → B` is a term with target type equal to the goal, terms of types `A₁, A₂, …, Aₙ, …` must be constructed in order to apply `f` and obtain a term of type `B`.

If none of the terms in the local context are able to eventually yield the target, the tactic fails. In principle, if a type can be constructed entirely in terms of function applications, this tactic should be able to find a term (this may not happen in practice due to looping).
-/
partial def findProofTU (mvar : MVarId) : TacticM Unit := do
  let (_, imvar) ← intros mvar -- introduce all the necessary hypotheses

  withMVarContext imvar do
    let tgtType ← getMVarType imvar -- the type of the goal

    for v in (← getLCtx) do -- scanning the local context
      let vType ← getTargetType v.type -- the target type of the local variables
      if !v.isAuxDecl then if (← isDefEq tgtType vType) then
        try
          let amvars ← apply imvar v.toExpr -- the goals obtained after applying the candidate term
          for amvar in amvars do
            findProofTU amvar -- recursively trying to solve the new goals
          done

          if (← getGoals).isEmpty then do
            logInfo m!"Proof complete - by {v.type}"
            return ()
        catch _ => continue

    -- throws an error if none of the terms of the local context can be used to construct the goal
    throwError m!"There are unsolved goals: \n\t{goalsToMessageData (← getGoals)}"

/-
This is the actual implementation of the tactic.
-/
syntax (name := findProof) "findProof" : tactic
@[tactic findProof] def findProofT : Tactic := fun stx => do
  findProofTU (← getMainGoal)


section examples

-- a convoluted example of the tactic in action
example : String → Float → (Unit → Int) → (Int → Nat) → (String → Unit) → Nat := by
  findProof

def convolutedexample : String → Float → (Unit → Int) → (Int → Nat) → (String → Unit) → Nat := by
  findProof

#print convolutedexample

def contrapose (P Q R : Type) : (P → Q) → ((Q → R) → (P → R)) := by
  findProof

#print contrapose

/-
P -> Q
Q -> ⊥
P
----
⊥
-/

def ident {A : Type} : A → A := by
  findProof

#print ident

def proj₁ {A B : Type} : A → (B → A) := by
  findProof

#print proj₁

def modusPonens {P Q : Type} : (P → Q) → (P → (Q)) := by
  findProof

#print modusPonens

def gelfand_naimark {A ℂ : Type} : A → ((A → ℂ) → ℂ) := by
  findProof

#print gelfand_naimark

def adjoint {V W F : Type} : (V → W) → ((W → F) → (V → (F))) := by
  findProof

#print adjoint

def differential {M N ℝ S : Type} (f : M → N) : ((M → ℝ) → S) → ((N → ℝ) → S) := by findProof

def differential' {M N ℝ : Type} (f : M → N) : ((M → ℝ) → ℝ) → ((N → ℝ) → ℝ) := differential f

#print differential


def cov_yoneda_fwd (A : Type) (F : Type → Type)
(η : (X : Type) → (A → X) → F X) : F A := by sorry

def cov_yoneda_fwd_simple (A : Type) (F : Type → Type) (η : (A → A) → F A) : F A := by findProof

#print cov_yoneda_fwd_simple

def cov_yoneda_bwd (A : Type) (F : Type → Type) (Fmap : (P Q : Type) → (P → Q) → (F P → F Q)) (a : F A) :
  ((X : Type) → ((A → X) → F X)) := by sorry

def cov_yoneda_bwd_simple (A X : Type) (F : Type → Type) (Fmap : (A → X) → (F A → F X)) (a : F A) :
  ((f : A → X) → F X) := by findProof

#print cov_yoneda_bwd

end examples
