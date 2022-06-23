import LeanUtils.Parity
import LeanUtils.Div

attribute [simp]
  -- -- addition
  --     -- swapping
  --     Nat.add_assoc
  --     Nat.add_comm
  --     Nat.add_left_comm
  --   -- multiplication
  --     -- swapping
  --     Nat.mul_assoc
  --     Nat.mul_comm
  --     Nat.mul_left_comm
  --     -- zero & one
  --     Nat.mul_zero
  --     Nat.zero_mul
  --     Nat.mul_one
  --     Nat.one_mul
  --   -- powers
  --     -- zero & one
  --     Nat.pow_zero
  --     -- succ
  --     Nat.pow_succ
  --   -- multiplication to addition
  --   Nat.left_distrib
  --   Nat.right_distrib
  -- defined in LeanUtils
  Nat.divisible
  Nat.even
  Nat.odd

  Nat.mod_rewrite
  Nat.even_rewrite
  Nat.odd_rewrite

  Nat.even_plus_even
  Nat.even_plus_odd
  Nat.odd_plus_odd
  Nat.div_plus_div
