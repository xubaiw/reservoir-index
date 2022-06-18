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

namespace VariableType

def toLeanType : VariableType → Type
  | str _  => String
  | strL   => String
  | double => Float
  | float  => Float
  | long   => UInt32
  | int    => UInt16
  | byte   => UInt8

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
  contents : Array String
  deriving Repr

abbrev Characteristics := Array Characteristic

inductive Observation
  | str (n : Fin 2045) (vs : Array String)
  | strL (vs : Array String)
  | double (vs : Array Float)
  | float (vs : Array Float)
  | long (vs : Array UInt32)
  | int (vs : Array UInt16)
  | byte (vs : Array UInt8)
  deriving Repr

abbrev Data := Array Observation

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
  deriving Repr

end Dta