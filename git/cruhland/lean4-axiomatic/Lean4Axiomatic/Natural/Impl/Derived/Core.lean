import Lean4Axiomatic.Operators
import Lean4Axiomatic.Natural.Core

namespace Lean4Axiomatic
namespace Natural

namespace Derived

variable {ℕ : Type}
variable [Core ℕ]
variable [Axioms.Base ℕ]

def ind_on
    {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ m, motive m → motive (step m)) : motive n :=
  Axioms.ind zero step n

def cases_on
    {motive : ℕ → Prop} (n : ℕ)
    (zero : motive 0) (step : ∀ n, motive (step n)) : motive n :=
  ind_on n zero (λ n ih => step n)

theorem step_neq {n : ℕ} : step n ≄ n := by
  apply ind_on (motive := λ n => step n ≄ n) n
  case zero =>
    show step 0 ≄ 0
    exact Axioms.step_neq_zero
  case step =>
    intro n (ih : step n ≄ n)
    show step (step n) ≄ step n
    intro (_ : step (step n) ≃ step n)
    show False
    apply ih
    show step n ≃ n
    exact AA.inject ‹step (step n) ≃ step n›

instance axioms_derived : Axioms.Derived ℕ where
  ind_on := ind_on
  cases_on := cases_on
  step_neq := step_neq

end Derived

end Natural
end Lean4Axiomatic
