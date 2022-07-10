import Std.Data.RBMap

namespace FuncDep

class CountParts_ (S : Type u) where
  μ : Type v
  α : Type w
  φ : S → μ → α

instance : CountParts_ String where
  μ := Char
  α := Nat
  φ haystack needle := haystack.foldl (fun acc x => acc + if x == needle then 1 else 0) 0

class CountParts (S : Type u) (μ : Type v) (α : Type w) where
  φ : S → μ → α

-- instance (i : CountParts S μₒ αₒ) : CountParts_ S where
--   μ := μₒ
--   α := αₒ
--   φ := i.φ

/- Somehow, Lean manages to see `Nat ~ CountParts_.α String` in the instance declaration! -/
instance : CountParts String Char Nat where
  φ haystack needle :=
    let y : Nat := FuncDep.instCountParts_String.φ haystack needle
    y + 1

instance [BEq α] : CountParts (List α) α Nat where
  φ haystack needle := haystack.foldl (fun acc x => if x == needle then 1 else 0) 0

instance : CountParts (List Nat) (List Nat) (Std.RBMap Nat Nat Ord.compare) where
  φ haystack needles := haystack.foldl (
    fun acc x =>
      needles.foldl (fun accₙ needle =>
        match accₙ.find? needle with
        | .none =>
          if x == needle then
            accₙ.insert needle 1
          else
            accₙ.insert needle 0
        | .some n =>
          if x == needle then
            accₙ.insert needle (n + 1)
          else
            accₙ
      ) acc
  ) Std.RBMap.empty

/-
failed to synthesize instance
  HAdd (CountParts_.α String) Nat ?m.419
-/
  -- φ haystack needle := (FuncDep.instCountParts_String.φ haystack needle : Nat) + 1

instance : CountParts Char Float Char where
  φ _ _ := '!'

-- instance : CountParts Char Nat Bool where
--   φ _ _ := true


/-
type mismatch
  CountParts_.φ haystack needle
has type
  CountParts_.α String : Type
but is expected to have type
  Float : Type
-/
-- instance : CountParts String Char Float where
--   φ haystack needle := FuncDep.instCountParts_String.φ haystack needle
