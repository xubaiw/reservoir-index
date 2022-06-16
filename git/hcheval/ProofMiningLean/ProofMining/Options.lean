import Lean.Data.Options 

open Lean 

register_option print_types : Bool := {
  defValue := false, 
  descr := "When displaying combinators, print their types."
}

