open HolKernel Parse boolLib bossLib pred_setTheory;

val _ = new_theory "untyped";

Datatype:
  untyped = True | False | IfThenElse untyped untyped untyped | 
            Zero | Succ untyped | Pred untyped | IsZero untyped
End

(* 3.3.1 Definition *)

Definition Consts_def:
  Consts (True) = { True } 
  ∧
  Consts (False) = { False }
  ∧
  Consts (Zero) = { Zero }
  ∧
  Consts (Succ t) = Consts t
  ∧
  Consts (Pred t) = Consts t
  ∧ 
  Consts (IsZero t) = Consts t
  ∧
  Consts (IfThenElse condition then_branch else_branch) =
         Consts(condition) ∪ 
         Consts(then_branch) ∪
         Consts(else_branch)
End

Definition Size_def:
  Size (True) = 1
  ∧
  Size (False) = 1
  ∧ 
  Size (Zero) = 1
  ∧ 
  Size (Succ t) = Size (t) + 1
  ∧
  Size (Pred t) = Size (t) + 1
  ∧ 
  Size (IsZero t) = Size (t) + 1
  ∧
  Size (IfThenElse condition then_branch else_branch) = 
    Size condition + Size then_branch + Size else_branch + 1
End

Definition ListMax_def:
  ListMax xs = FOLDL MAX 0 xs
End

Definition Depth_def:
  Depth (True) = 1
  ∧
  Depth (False) = 1
  ∧
  Depth (Zero) = 1
  ∧ 
  Depth (Succ t) = Depth t + 1
  ∧
  Depth (Pred t) = Depth t + 1
  ∧
  Depth (IsZero t) = Depth t + 1
  ∧
  Depth (IfThenElse condition then_branch else_branch) = 
    ListMax [ Depth condition;
              Depth then_branch;
              Depth else_branch ]
End

Theorem consts_finite: (* consts_le_size calculations need this fact *)
  FINITE(Consts t)
Proof
  Induct_on `t` >> simp [Consts_def,pred_setTheory.FINITE_UNION]
QED

Theorem consts_le_size: (* Pierce 3.3.3 Lemma *)
  CARD(Consts t) ≤ Size t
Proof
  Induct_on `t` >> gs [Consts_def, Size_def, pred_setTheory.CARD_UNION_EQN, consts_finite] 
QED

(* Pierce 3.3.4 tells us three methods to prove things generally for untyped
 * programs: induction on depth, induction on size and structural induction
 *
 * The last, structural induction is built-in in HOL4: for a datatype, it
 * provides an adequate structural induction rule. For the
 * untyped datatype above, HOL4 generates the following
 * induction theorem:
 *
 * theorem "untyped_induction";
 *
 * Now I will prove rules for induction on depth and
 * induction on size.
 *
 *)

Theorem untyped_depth_induction:
  ∀P.( ∀s.( ∀r. ((Depth(r) < Depth(s) ⇒ P(r)) ⇒ P(s)))) ⇒ ∀s.P(s)
Proof
  measureInduct_on `Depth s`
  simp [Depth_def]

val _ = export_theory();