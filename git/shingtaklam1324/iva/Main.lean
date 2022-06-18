import Iva.Polynomial.ToString
import Iva.Polynomial.Buchberger
import Iva.Monomial.Ordering

inductive Vars
| X 
| Y
deriving BEq, Hashable

open Vars in
section

instance : Fintype Vars where
  univ := [X, Y]
  is_univ := sorry

instance : ToString Vars where
  toString | X => "x"
           | Y => "y"

end

abbrev R := Float
abbrev o := Monomial.Ordering.grLex Vars

open Polynomial in
section

instance : Add (Polynomial R Vars) := ⟨(· +[o] ·)⟩
instance : Mul (Polynomial R Vars) := ⟨(· *[o] ·)⟩
instance : Sub (Polynomial R Vars) := ⟨(· -[o] ·)⟩
instance : Pow (Polynomial R Vars) Nat := ⟨(· ^[o] ·)⟩

end

abbrev x : Polynomial R Vars := Polynomial.ofVar Vars.X
abbrev y : Polynomial R Vars := Polynomial.ofVar Vars.Y

instance : Dvd R := ⟨λ _ _ => true⟩ -- We are in a field, and all the coeffs are nonzero

abbrev f₁ := x^3 - (2 : R) * (x * y)
abbrev f₂ := x^2 * y - ((2 : R) * (y^2) : Polynomial R Vars) + x 

abbrev I := [f₁, f₂]

def List.perLine [ToString α] (l : List α) : String :=
  "\n".intercalate <| l.map toString

def main : IO Unit :=
  let res := buchberger I o
  println!"A Gröbner basis for:\n\n{I.perLine} \n\nwith the grLex order is:\n\n{res.perLine}"

#eval main
