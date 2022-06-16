

class Mem (α : outParam $ Type u) (γ : Type v) where
  mem : α → γ → Prop

infix:50 " ∈ " => Mem.mem

/-
  Missing stuff about lists.
  Much of this is translated ad litteram from Lean3 mathlib
-/

namespace List

  def mem (a : α) : List α → Prop
  | [] => False
  | (b :: l) => a = b ∨ mem a l

  instance : Mem α (List α) := ⟨mem⟩

  instance {α : Type _} : Mem α (List α) := ⟨mem⟩

  @[simp] def nth : List α → Nat → Option α 
  | [], _ => none
  | a :: _, 0 => a
  | _ :: l, n + 1 => nth l n

  inductive Sublist : List α → List α → Prop 
  | slnil : Sublist [] []
  | cons : Sublist x y → Sublist x (a :: y)
  | cons₂ : Sublist x y → Sublist (a :: x) (a :: y)

  infix:50 " <+ " => Sublist

  /-
    An embedding from the list `xs` to the list `ys`
  -/
  -- structure Embedding (xs ys : List α) where 
  --   emb : Nat → Nat 
  --   emb_ok : xs.nth i = some x → ys.nth i = some x

  /-
    An embedding of the list `xs` into the list `ys` 
    is a mapping `emb` between indices preserving mapping the elements in `xs` 
    to an equal element in `ys`
  -/
  structure Embedding (xs ys : List α) where 
    emb : Nat → Nat 
    emb_inj : xs.nth i = some x → ys.nth (emb i) = some x

end List 


namespace Option 

  @[simp] def get!! {α : Type _} [Inhabited α] : Option α → α 
  | some x => x
  | none => Inhabited.default

end Option



def iterate {α : Sort _} (op : α → α) (n : Nat) (a : α) : α :=
match n with 
| 0 => a 
| n + 1 => op (iterate op n a)

macro "TODO_ALEX" : term => `(sorry)
macro "TODO_ALEX" : tactic => `(sorry)

macro "TODO_HORATIU" : term => `(sorry)
macro "TODO_HORATIU" : tactic => `(sorry)
