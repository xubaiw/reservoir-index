import TBA.While.Semantics

namespace While

namespace Optimisation

def foldExpr (σ : State) : Expr → Expr
  | .const v => Expr.const v
  | .var x =>
    match σ x with
    | some v => Expr.const v
    | none   => Expr.var x
  | .binop e₁ op e₂ =>
    match foldExpr σ e₁, foldExpr σ e₂ with
    | .const v₁, .const v₂ =>
      match op.eval v₁ v₂ with
      | some v => Expr.const v
      | none   => Expr.binop v₁ op v₂
    | e₁', e₂' => Expr.binop e₁' op e₂'

def foldCom (σ : State) : Com → (Com × State)
  | .skip => (Com.skip, σ)
  | .ass x e => 
      match foldExpr σ e with
      | .const v => (Com.ass x v, σ[x ↦ v])
      | e'       => (Com.ass x e', σ[x ↦ none])
  | .seq c₁ c₂ =>
    have (c₁', σ')  := foldCom σ c₁
    have (c₂', σ'') := foldCom σ' c₂
    (Com.seq c₁' c₂', σ'')
  | .cond b cₜ cₑ => 
    match foldExpr σ b with
    | .const true  => foldCom σ cₜ
    | .const false => foldCom σ cₑ
    | b' =>
      have ((cₜ', σₜ), (cₑ', σₑ)) := (foldCom σ cₜ, foldCom σ cₑ)
      (Com.cond b' cₜ' cₑ', λ k => if σₜ k = σₑ k then σₜ k else none)
  | .while b c =>
    match foldExpr σ b with
    | .const false => (Com.skip, σ)
    | _            => (Com.while b (foldCom Map.empty c).1, Map.empty)

def optimise : Com → Com := λ c => (foldCom Map.empty c).1

end Optimisation

end While
