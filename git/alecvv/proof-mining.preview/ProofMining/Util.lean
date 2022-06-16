

class Mem (α : outParam $ Type u) (γ : Type v) where
  mem : α → γ → Prop

infix:50 " ∈ " => Mem.mem


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

