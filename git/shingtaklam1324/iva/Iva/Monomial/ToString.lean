import Iva.Monomial
import Iva.Data.Fintype

partial def toSuperscript : Nat → String
| 0 => "⁰"
| 1 => "¹"
| 2 => "²"
| 3 => "³"
| 4 => "⁴"
| 5 => "⁵"
| 6 => "⁶"
| 7 => "⁷"
| 8 => "⁸"
| 9 => "⁹"
| n => toSuperscript (n / 10) ++ toSuperscript (n % 10)

variable {α : Type u} [BEq α] [Hashable α] [Fintype α] [ToString α]

instance : ToString (Monomial α) where
  toString m :=
    let res := List.univ.foldl (init := "") λ s a => 
      if m.exponent a == 0 then 
        s 
      else if m.exponent a == 1 then
        s ++ toString a
      else
        s ++ toString a ++ toSuperscript (m.exponent a)
    if res == "" then "1" else res
