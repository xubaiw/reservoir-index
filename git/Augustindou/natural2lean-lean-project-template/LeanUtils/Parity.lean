import LeanUtils.Div
import Mathlib.Tactic.Ring

/- Parity : functions and theorems related to parity -/

namespace Nat
  def even (a : Nat) : Prop := a % 2 = 0
  def odd (a : Nat) : Prop := a % 2 = 1

  theorem even_rewrite {a : Nat} : even a ↔ ∃ (n : Nat), a = 2 * n := 
    Iff.intro
      (by
        intro h
        rw [even, mod_rewrite] at h
        simp_all)
      (by 
        intro h
        have ⟨n, hn⟩ := h
        rw [hn, even, mod_rewrite]
        exact ⟨_, by rfl⟩)
  
  theorem odd_rewrite {a : Nat} : odd a ↔ ∃ (n : Nat), a = 2 * n + 1 :=
    Iff.intro
      (by
        intro h
        rw [odd, mod_rewrite] at h
        simp_all)
      (by 
        intro h
        have ⟨n, hn⟩ := h
        rw [hn, odd, mod_rewrite]
        exact ⟨_, by rfl⟩)

  theorem even_plus_even {a b : Nat} : even a → even b → even (a + b) := by 
    intros h₁ h₂
    rw [even_rewrite] at h₁ h₂
    have ⟨n, hn⟩ := h₁
    have ⟨m, hm⟩ := h₂
    rw [hn, hm]
    apply even_rewrite.mpr
    exact ⟨n+m, by ring⟩

  theorem even_plus_odd {a b : Nat} : even a → odd b → odd (a + b) := by
    intros h₁ h₂
    rw [even_rewrite] at h₁
    rw [odd_rewrite] at h₂
    have ⟨n, hn⟩ := h₁
    have ⟨m, hm⟩ := h₂
    rw [hn, hm]
    apply odd_rewrite.mpr
    exact ⟨n+m, by ring⟩

  theorem odd_plus_odd {a b : Nat} : odd a → odd b → even (a + b) := by
    intros h₁ h₂
    rw [odd_rewrite] at h₁ h₂
    have ⟨n, hn⟩ := h₁
    have ⟨m, hm⟩ := h₂
    rw [hn, hm]
    apply even_rewrite.mpr
    exact ⟨n+m+1, by ring⟩


end Nat
