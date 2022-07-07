import Std.Data.HashMap

open Std

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
  | strLIndex
  | double
  | float
  | long
  | int
  | byte
  deriving Repr

namespace VariableType

end VariableType

abbrev VariableTypes := Array VariableType

abbrev VarNames := Array String

abbrev SortList := Array UInt16

abbrev Formats := Array String

abbrev ValueLabelNames := Array String

abbrev VariableLabels := Array String

structure Characteristic where
  varname : String
  charname : String
  contents : String
  deriving Repr

abbrev Characteristics := Array Characteristic

inductive Value
  | str (n : Fin 2045) (v : String)
  | strLIndex (v : UInt32 × UInt64)
  | double (v : Float)
  | float (v : Float)
  | long (v : UInt32)
  | int (v : UInt16)
  | byte (v : UInt8)
  deriving Repr

abbrev Observation := Array Value

abbrev Data := Array Observation

structure GSO where
  v : UInt32
  o : UInt64
  binary : Bool
  len : UInt32
  contents : String
  deriving Repr

abbrev StrLs := Array GSO

structure Dta where
  header : Header
  map : Map
  variableTypes : VariableTypes
  varnames : VarNames
  sortlist : SortList
  formats : Formats
  valueLabelNames : ValueLabelNames
  variableLabels : VariableLabels
  characteristics : Characteristics
  data : Data
  strLs : StrLs
  deriving Repr

end Dta
