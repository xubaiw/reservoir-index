/- Parity : functions and theorems related to parity -/

namespace Nat
  def even (a : Nat) : Prop := ∃ (n : Nat), a = 2 * n
  def odd (a : Nat) : Prop := ∃ (n : Nat), a = 2 * n + 1
end Nat
