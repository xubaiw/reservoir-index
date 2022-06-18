namespace Dta

/-- Stata .dta specification version -/
inductive Release
  | /-- Stata  8 -/ «113»
  | /-- Stata 10 -/ «114»
  | /-- Stata 12 -/ «115»
  | /-- Stata 13 -/ «117»
  | /-- Stata 14 - 17 -/ «118»
  | /-- Stata 15 - 17 (when dataset has more than 32,767 variables) -/ «119»
  deriving DecidableEq, Repr

/-- Byteorder of .dta file -/
inductive Byteorder
  | /-- Most Significant byte First -/ msf
  | /-- Least Significant byte First -/ lsf
  deriving Repr

def typeK : Release → Type
  | .«119» => UInt32
  | _      => UInt16

namespace typeK

instance : Repr (typeK r) where
  reprPrec k _ := by
    cases r
    <;> simp [typeK] at k
    <;> exact repr k

def toNat : typeK r → Nat := by
  cases r
  <;> simp [typeK]
  <;> exact (·.toNat)

end typeK

structure Header where
  release : Release
  byteorder : Byteorder
  k : typeK release
  n : UInt64
  label : String
  timestamp : Option String
  deriving Repr

abbrev Map := Array UInt64

inductive VariableType
  | str (n : Fin 2045)
  | strL
  | double
  | float
  | long
  | int
  | byte
  deriving Repr

abbrev VariableTypes := Array VariableType

abbrev VarNames := Array String

structure Dta where
  header : Header
  map : Map
  variableTypes : VariableTypes
  varnames : VarNames
  deriving Repr

end Dta