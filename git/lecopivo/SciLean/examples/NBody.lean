import SciLean.Mechanics
import SciLean.Operators.ODE
import SciLean.Solver 
import SciLean.Tactic.LiftLimit
import SciLean.Tactic.FinishImpl
import SciLean.Data.PowType
import SciLean.Core.Extra
import SciLean.Functions

open SciLean

set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 500000

def H (n : Nat) (ε : ℝ) (m : Idx n → ℝ) (x p : ((ℝ^(3:Nat))^n)) : ℝ := 
  (∑ i, (1/(2*m i)) * ∥p[i]∥²)
  +
  (∑ i j, (m i*m j) * ∥x[i] - x[j]∥^{(-1:ℝ),ε})
argument p [Fact (ε≠0)] [Fact (n≠0)]
  isSmooth, hasAdjDiff, adjDiff
argument x [Fact (ε≠0)] [Fact (n≠0)]
  isSmooth, hasAdjDiff,
  adjDiff by
    simp[H]
    simp [sum_into_lambda]
    simp [← sum_of_add]
    
def solver (steps : ℕ) (n : Nat) [Fact (n≠0)] (ε : ℝ) [Fact (ε≠0)] (m : Idx n → ℝ)
  : Impl (ode_solve (HamiltonianSystem (H n ε m))) :=
by
  -- Unfold Hamiltonian definition and compute gradients
  simp[HamiltonianSystem]
  
  -- Apply RK4 method
  rw [ode_solve_fixed_dt runge_kutta4_step]
  lift_limit steps "Number of ODE solver steps."; admit; simp
   
  finish_impl
