import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
open SubNegMonoid

-- currently mainly experiments

variable {A : Type} [abg : AddCommGroup A]

def f (a: A) : ℤ → A := 
  fun n => abg.gsmul n a

theorem gsmul_succ (n: ℤ) (x : A) : gsmul (n+1) x = x + gsmul n x  := by 
    cases n  
    case ofNat k => 
      apply abg.gsmul_succ'
    case negSucc k => 
      induction k with
      | zero => 
        simp
        simp [add_zero]
        have l : -[1+ 0] + 1 = 0 := by rfl
        rw [l]
        have l₀ : gsmul 0 x = 0 := by apply abg.gsmul_zero'
        rw [l₀]
        simp
        rw [abg.gsmul_neg']
        simp
        let l : gsmul 1 x = 
                x + gsmul (0) x := abg.gsmul_succ' 0 x
        rw [l]
        rw [l₀]
        simp
      | succ l ih => 
        have l₀ : -[1+ Nat.succ l] + 1 = -[1+ l] := by rfl
        rw [l₀]
        rw [abg.gsmul_neg']
        rw [abg.gsmul_neg']
        simp

        let l₁ := abg.gsmul_succ' (l + 1) x
        simp at l₁
        rw [l₁]
        simp
        let y := gsmul (l + 1) x
        show -y = x + -(x + y)
        apply Eq.symm
        conv =>
          lhs
          arg 2
          rw [add_comm]
        
        apply @add_left_cancel _ _ _ y _ _
        rw [← add_assoc, add_right_neg, add_right_neg]



        
#check add_left_cancel
    
#check neg_add_self

theorem isHomPos (x : A) (n m: Nat) : f x (n + m) = f x n + f x m :=
  by 
    induction m with
    | zero =>
      simp [f]
      rw [abg.gsmul_zero']
      simp     
    | succ k ih =>
      simp [f]
      simp [f] at ih
      rw [← add_assoc]
      simp
      let l₁ := abg.gsmul_succ' k x

      simp at l₁
      rw [l₁]
      simp
      let l₂ := abg.gsmul_succ' (n + k) x
      simp at l₂
      rw [l₂] 
      rw [ih]
      simp
      conv =>
        lhs
        rw [← add_assoc]
        arg 1
        rw [add_comm]
      rw [← add_assoc]

