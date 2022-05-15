inductive form where 
  | atom : Nat → form 
  | bot : form
  | impl : form → form → form 
  | box : form → form 

notation:40 "¬"p => form.impl p (form.bot)
infix:50 "→" => form.impl 
notation p "∧" q => ¬(p → (¬q))
notation p "∨" q => ¬((¬p) ∧ (¬q))
prefix:80 "□" => form.box 
notation "⋄"p => ¬(□(¬p))
notation "⊥" => form.bot
notation "⊤" => ¬⊥ 