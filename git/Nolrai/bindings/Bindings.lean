import Init.Data.Format

def hello := "world"

inductive Lambda : Nat → Type u where
  | Var : Fin n → Lambda n
  | App : Lambda n → Lambda n → Lambda n
  | Abs : Lambda (n+1) → Lambda n

open Lambda

infix:70 "ᵛ" => λ n v => (Var v : Lambda n)

instance {n} : CoeFun (Lambda n) (λ _ => Lambda n → Lambda n) where
  coe := App

def ID : Lambda n → Lambda n := λ r => App (Abs $ Var ⟨n, Nat.lt_of_succ_le (Nat.le_refl _) ⟩) r

theorem Eq.comm : a = b ↔ b = a :=
  ⟨Eq.symm, Eq.symm⟩

def push_arg {n depth : Nat} : Lambda (n + depth) → Lambda (n + (depth + 1))
  | Var v => Var $
    if v < n then
      ⟨v.val, by 
        apply Nat.lt_trans v.isLt
        rw [← Nat.add_assoc, Nat.add_one]
        apply Nat.lt_of_succ_le
        apply Nat.le_of_eq
        rfl
      ⟩
    else
      ⟨v.val + 1, by
        simp [← Nat.add_assoc, Nat.add_one]
        apply Nat.succ_lt_succ
        exact v.isLt
      ⟩
  | Abs body => Abs (push_arg body)
  | App l r => App (push_arg l) (push_arg r)

def beta_aux (arg : Lambda (n + depth)) (body : Lambda (n + depth + 1)) : Lambda (n + depth) :=
  match body with
  | Var v => 
    if v_lt : v.val < n 
      then by
        apply Var ∘ Fin.mk v.val
        apply Nat.lt_of_lt_of_le v_lt
        apply Nat.le_add_right
    else if v_eq : v = n
      then arg
      else
        have n_lt_v : n < v.val := by
          have ⟨v', vh⟩ := v
          clear body arg
          simp at *
          clear depth vh v
          apply Nat.lt_of_le_of_ne
          apply Nat.ge_of_not_lt
          exact v_lt
          rw [Eq.comm]
          exact v_eq 
        have h : v.val - 1 < n + depth := by
          suffices v.val - 1 + 1 < n + depth + 1 by
            apply Nat.lt_of_succ_lt_succ
            apply this
          rw [Nat.sub_add_cancel]
          exact v.isLt
          apply Nat.succ_le_of_lt
          apply Nat.lt_of_le_of_lt _ n_lt_v
          apply Nat.zero_le
        Var ⟨v.val - 1, h⟩
  | App l r => App (beta_aux arg l) (beta_aux arg r)
  | Abs newBody => 
    have newArg : Lambda (n + (depth + 1)) := push_arg arg
    Abs (beta_aux newArg newBody)

def beta_aux2 : Lambda n → Lambda (n + 1) → Lambda n := by
  rw [← Nat.add_zero n]
  apply @beta_aux n 0

inductive beta : Lambda n → Lambda n → Prop
  | here (body arg result) : result = beta_aux2 arg body → beta (App (Abs body) arg) result
  | left (xs : beta x y) : beta (App x z) (App y z)
  | right (xs : beta x y) : beta (App z x) (App z y)
  | abs (xs : beta x y) : beta (Abs x) (Abs y)

inductive RTC (R : α → α → Prop) : α → α → Prop where
  | refl : RTC R a a
  | step : R a b → RTC R b c → RTC R a c

theorem RTC.trans : RTC R a b → RTC R b c → RTC R a c := by
  intros ab bc
  induction ab
  case refl => 
    exact bc
  case step a' b' c' x _ xs_ih =>
    apply RTC.step x (xs_ih bc)

infix:50 "~>" => RTC beta

example : ∀ r : Lambda n, ID r ~> r := by
  intros r
  apply RTC.step _ RTC.refl
  apply beta.here
  rw [beta_aux2]
  simp [beta_aux, Eq.mpr]

def Lambda.reprPrec' : Lambda n → Nat → Std.Format
  | Var v, prec => reprPrec n prec ++ "ᵛ" ++  reprPrec v prec
  | App l r, prec => Std.Format.paren (reprPrec' l prec ++ " " ++ reprPrec' r prec)
  | Abs body, prec => Std.Format.paren $ "λ." ++ Repr.addAppParen (body.reprPrec' (prec + 1)) prec 

instance : Repr (Lambda n) where
  reprPrec l n := Lambda.reprPrec' l n