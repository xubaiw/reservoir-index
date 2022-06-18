import WaterSortPuzzle.Defs

nsmeapce
/--
给定k的求解
-/
def solveAux (config : PuzzleConfig m h n) : Option (Solution n) := sorry

/--
求解函数
-/
partial def solve (config : PuzzleConfig m h n) : Solution n :=
  match solveAux config with
  | some solution => solution
  | none => solve { config with k := config.k + 1 }

/--
证明 k ≥ n 时，一定有解
-/
theorem solveAux_k_ge_n : ∀ {config : PuzzleConfig m h n}, config.k ≥ n → Solution n := sorry