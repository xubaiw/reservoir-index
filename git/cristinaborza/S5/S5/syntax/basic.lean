import S5.context

inductive prf : ctx → form → Prop where 
| ax { Γ } { p } (h : p ∈ Γ) : prf Γ p 
| pl1 { Γ } { p q } : prf Γ (p → (q → p))
| pl2 { Γ } { p q r } : prf Γ ((p → (q → r)) → ((p → q) → (p → r)))
| pl3 { Γ } { p q } : prf Γ (((¬p) → (¬q)) → (((¬p) → q) → p))
| mp { Γ } { p q } (hpq : prf Γ (p → q)) (hp : prf Γ p) : prf Γ q
| k { Γ } { p q } : prf Γ (□(p → q) → (□p → □q))
| t { Γ } { p } : prf Γ (□p → p) 
| s4 { Γ } { p } : prf Γ (□p → □□p) 
| s5 { Γ } { p } : prf Γ (¬(□p) → □(¬(□p)))
| nec { Γ } { p } (h : (prf [] p)) : prf Γ (□p)
 
notation Γ "⊢ₛ₅" p => prf Γ p 
notation "⊢ₛ₅" p => prf [] p 
 