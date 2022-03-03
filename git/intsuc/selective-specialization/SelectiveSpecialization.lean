abbrev Lvl := Nat

abbrev Erased := Bool

inductive Raw where
  | var   : String → Raw
  | «let» : String → Raw → Raw → Raw → Raw
  | abs   : String → Raw → Raw
  | app   : Raw → Raw → Raw
  | spec  : Raw → Raw → Raw
  | «fun» : Erased → String → Raw → Raw → Raw
  | unit  : Raw
  | top   : Raw
  | type  : Raw

inductive Exp where
  | var   : String → Lvl → Exp
  | «let» : String → Exp → Exp → Exp → Exp
  | abs   : String → Exp → Exp
  | app   : Exp → Exp → Exp
  | «fun» : Erased → String → Exp → Exp → Exp
  | unit  : Exp
  | top   : Exp
  | type  : Exp
  deriving Inhabited

instance : ToString Exp where
  toString :=
    let rec go
      | Exp.var s₁ _        => s!"${s₁}"
      | Exp.let s₁ e₂ e₃ e₄ => s!"let {s₁} : {go e₂} := {go e₃}; {go e₄}"
      | Exp.abs s₁ e₂       => s!"fun {s₁} => {go e₂}"
      | Exp.app e₁ e₂       => s!"{go e₁}({go e₂})"
      | Exp.fun b₁ s₂ e₃ e₄ => if b₁ then s!"[{s₂} : {go e₃}] → {go e₄}" else s!"({s₂} : {go e₃}) → {go e₄}"
      | Exp.unit            => "()"
      | Exp.top             => "⊤"
      | Exp.type            => "*"
    go

mutual
  inductive Val where
    | var   : String → Lvl → Val
    | abs   : String → Clo → Val
    | app   : Val → Val → Val
    | «fun» : Erased → String → Val → Clo → Val
    | unit  : Val
    | top   : Val
    | type  : Val
    deriving Inhabited

  inductive Clo where
    | mk : Array Val → Exp → Clo
end

abbrev Env := Array Val

mutual
  partial def eval (Ξ : Env) : Exp → Val
    | Exp.var s₁ n₂       => Val.var s₁ n₂
    | Exp.let _ _ e₃ e₄   => eval (Ξ.push (eval Ξ e₃)) e₄
    | Exp.abs s₁ e₂       => Val.abs s₁ (Clo.mk Ξ e₂)
    | Exp.app e₁ e₂       =>
      match eval Ξ e₁, eval Ξ e₂ with
      | Val.abs _ c₁, v₂ => apply c₁ v₂
      | v₁,           v₂ => Val.app v₁ v₂
    | Exp.fun b₁ s₂ e₃ e₄ => Val.fun b₁ s₂ (eval Ξ e₃) (Clo.mk Ξ e₄)
    | Exp.unit            => Val.unit
    | Exp.top             => Val.top
    | Exp.type            => Val.type

  partial def apply : Clo → Val → Val
    | Clo.mk Ξ e, v => eval (Ξ.push v) e
end

partial def quote (n : Lvl) : Val → Exp
  | Val.var s₁ n₂       => Exp.var s₁ n₂
  | Val.abs s₁ c₂       => Exp.abs s₁ (quote n.succ (apply c₂ (Val.var s₁ n)))
  | Val.app v₁ v₂       => Exp.app (quote n v₁) (quote n v₂)
  | Val.fun b₁ s₂ v₃ c₄ => Exp.fun b₁ s₂ (quote n v₃) (quote n (apply c₄ (Val.var s₂ n)))
  | Val.unit            => Exp.unit
  | Val.top             => Exp.top
  | Val.type            => Exp.type

instance : ToString Val where
  toString v := toString (quote 0 v)

partial def conv (n : Lvl) : Val → Val → Bool
  | Val.var _ n₁₂,           Val.var _ n₂₂         => n₁₂ == n₂₂
  | Val.abs s₁₁ c₁₂,         Val.abs _ c₂₂         => let x := Val.var s₁₁ n; conv n.succ (apply c₁₂ x) (apply c₂₂ x)
  | Val.app v₁₁ v₁₂,         Val.app v₂₁ v₂₂       => conv n v₁₁ v₂₁ && conv n v₁₂ v₂₂
  | Val.fun b₁₁ s₁₂ v₁₃ c₁₄, Val.fun b₂₁ _ v₂₃ c₂₄ => b₁₁ == b₂₁ && conv n v₁₃ v₂₃ && let x := Val.var s₁₂ n; conv n.succ (apply c₁₄ x) (apply c₂₄ x)
  | Val.type,                Val.type              => true
  | _,                       _                     => false

abbrev Ctx := Array (Erased × String × Val)

abbrev M := Except String

mutual
  partial def infer (Ξ : Env) (Γ : Ctx) (Φ : Erased) : Raw → M (Exp × Val)
    | Raw.var s₁          =>
      match Γ.findIdx? (fun (_, s, _) => s == s₁) with
      | none   => Except.error "variable not found"
      | some n =>
        let (b, s, t) := Γ.get! n
        if Φ == b then (Exp.var s n, t) else Except.error "erased"
    | Raw.let s₁ r₂ r₃ r₄ => do
      let e₂ ← check Ξ Γ true r₂ Val.type
      let v₂ := eval Ξ e₂
      let e₃ ← check Ξ Γ Φ r₃ v₂
      let v₃ := eval Ξ e₃
      let (e₄, t₄) ← infer (Ξ.push v₃) (Γ.push (Φ, s₁, v₂)) Φ r₄
      (Exp.let s₁ e₂ e₃ e₄, t₄)
    | Raw.abs ..          => Except.error "failed to infer abs"
    | Raw.app r₁ r₂       => do
      let (e₁, t₁) ← infer Ξ Γ Φ r₁
      match t₁ with
      | Val.fun b₁₁ s₁₂ t₁₃ c₁₄ =>
        let e₂ ← check Ξ Γ b₁₁ r₂ t₁₃
        (Exp.app e₁ e₂, apply c₁₄ (eval Ξ e₂))
      | _               => Except.error "fun expected"
    | Raw.spec r₁ r₂      => do
      let (e₁, t₁) ← infer Ξ Γ Φ r₁
      match t₁ with
      | Val.fun b₁₁@true s₁₂ t₁₃ c₁₄ =>
        let _ ← check Ξ Γ b₁₁ r₂ t₁₃
        let e₂ := Exp.unit
        (Exp.app e₁ e₂, apply c₁₄ (eval Ξ e₂)) -- TODO: type
      | _               => Except.error "erased fun expected"
    | Raw.fun b₁ s₂ r₃ r₄ => do
      let e₃ ← check Ξ Γ true r₃ Val.type
      let e₄ ← check Ξ Γ true r₄ Val.type
      (Exp.fun b₁ s₂ e₃ e₄, Val.type)
    | Raw.unit            => (Exp.unit, Val.top)
    | Raw.top             => (Exp.top, Val.type)
    | Raw.type            => (Exp.type, Val.type)

  partial def check (Ξ : Env) (Γ : Ctx) (Φ : Erased) : Raw → Val → M Exp
    | Raw.let s₁ r₂ r₃ r₄, v                   => do
      let e₂ ← check Ξ Γ true r₂ Val.type
      let v₂ := eval Ξ e₂
      let e₃ ← check Ξ Γ Φ r₃ v₂
      let v₃ := eval Ξ e₃
      let e₄ ← check (Ξ.push v₃) (Γ.push (Φ, s₁, v₂)) Φ r₄ v
      Exp.let s₁ e₂ e₃ e₄
    | Raw.abs s₁ r₂,       Val.fun b₁ s₂ v₃ c₄ => do
      let x := Val.var s₁ Ξ.size
      let e₂ ← check (Ξ.push x) (Γ.push (b₁, s₁, v₃)) Φ r₂ (apply c₄ x)
      Exp.abs s₁ e₂
    | r,                   v                   => do
      let (e, t) ← infer Ξ Γ Φ r
      if conv Ξ.size t v then e else Except.error "type mismatch"
end

#eval infer #[] #[] false $ Raw.let "f" (Raw.fun false "α" Raw.type Raw.type) (Raw.abs "a" (Raw.var "a")) Raw.type
#eval infer #[] #[] false $ Raw.let "f" (Raw.fun true "α" Raw.type Raw.type) (Raw.abs "a" (Raw.var "a")) Raw.type

#eval infer #[] #[] false $ Raw.let "f" (Raw.fun false "α" Raw.type Raw.type) (Raw.abs "a" Raw.type) (Raw.spec (Raw.var "f") Raw.type)
#eval infer #[] #[] false $ Raw.let "f" (Raw.fun false "α" Raw.type Raw.type) (Raw.abs "a" Raw.type) (Raw.app (Raw.var "f") Raw.type)
#eval infer #[] #[] false $ Raw.let "f" (Raw.fun true "α" Raw.type Raw.type) (Raw.abs "a" Raw.type) (Raw.spec (Raw.var "f") Raw.type)
