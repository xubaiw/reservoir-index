import Dta.Basic
import Dta.Float
import Parsec

open Parsec ByteArrayParser

namespace Dta

def wrapped (tag : String) (p : ByteArrayParser α) : ByteArrayParser α := do
  expectS s!"<{tag}>"
  let s ← p
  expectS s!"</{tag}>"
  return s

def wrappedArray (tag : String) (num : Nat) (p : ByteArrayParser α) : ByteArrayParser (Array α) := do
  wrapped tag (readArray num p)

def wrappedArrayString (tag : String) (num length : Nat) (f : String → String := (·.replace "\x00" "")) : ByteArrayParser (Array String) := do
  wrappedArray tag num s
where
  s := do
    let s ← readString length
    return f s

@[inline]
partial def manyCore (p : ByteArrayParser α) (acc : Array α) : ByteArrayParser (Array α) := do
  try
    let res ← p
    manyCore p (acc.push res)
  catch _ =>
    return acc

@[inline]
def many (p : ByteArrayParser α) : ByteArrayParser $ Array α := manyCore p #[]

partial def readString' : ByteArrayParser String := do
  let mut arr := ByteArray.empty
  repeat do
    let s ← peek
    if s = 0 then
      break
    arr := arr.push s
  return arr |> String.fromUTF8Unchecked

def release : ByteArrayParser Release := do
  match ←readString 3 with
  | "113" => return .«113»
  | "114" => return .«114»
  | "115" => return .«115»
  | "117" => return .«117»
  | "118" => return .«118»
  | "119" => return .«119»
  | _     => error "invalid <release> field"

def byteorder : ByteArrayParser Byteorder := do
  match ←readString 3 with
  | "LSF" => return .lsf
  | "MSF" => return .msf
  | _      => error "invalid <byteorder> field"

def read16 : Byteorder → ByteArrayParser UInt16
| .lsf => read16LE
| .msf => read16BE

def read32 : Byteorder → ByteArrayParser UInt32
| .lsf => read32LE
| .msf => read32BE

def read64 : Byteorder → ByteArrayParser UInt64
| .lsf => read64LE
| .msf => read64BE

def k (r : Release) (e : Byteorder) : ByteArrayParser (typeK r) := by
  cases r <;> simp [typeK]
  repeat exact read16 e
  exact read32 e

def n (e : Byteorder) := read64 e

def label (e : Byteorder) : ByteArrayParser String := do
  let length ← read16 e
  readString length.toNat

def timestamp? : ByteArrayParser (Option String) := do
  let length ← read8
  match length with
  |  0 => return none
  | 17 => return (←readString 17)
  |  _ => error "length of timestamp must be 0 or 17"

def header : ByteArrayParser Header := wrapped "header" do
  let r ← wrapped "release" release
  let e ← wrapped "byteorder" byteorder
  let k ← wrapped "K" (k r e)
  let n ← wrapped "N" (n e)
  let label ← wrapped "label" (label e)
  let timestamp? ← wrapped "timestamp" timestamp?
  return ⟨r, e, k, n, label, timestamp?⟩

def map (e : Byteorder) : ByteArrayParser Map := do
  wrappedArray "map" 14 (read64 e)

def variableTypes (k : typeK r) (e : Byteorder) : ByteArrayParser VariableTypes := do
  expectS "<variable_types>"
  let mut arr := #[]
  for x in ←readArray k.toNat (read16 e) do
    match x with
    | 32768 => arr := arr.push .strL
    | 65526 => arr := arr.push .double
    | 65527 => arr := arr.push .float
    | 65528 => arr := arr.push .long
    | 65529 => arr := arr.push .int
    | 65530 => arr := arr.push .byte
    | x =>
      let x' := x.toNat - 1
      if h : x' < 2045 then
        arr := arr.push <| .str ⟨x', h⟩
      else
        throw (←error "variable type out of range")
  expectS "</variable_types>"
  return arr

def varnames (k : typeK r) : ByteArrayParser VarNames :=
  wrappedArrayString "varnames" k.toNat 129

def sortlist (k : typeK r) (e : Byteorder) : ByteArrayParser SortList := do
  wrappedArray "sortlist" (k.toNat + 1) (read16 e)

def formats (k : typeK r) : ByteArrayParser Formats :=
  wrappedArrayString "formats" k.toNat 57

def valueLabelNames (k : typeK r) : ByteArrayParser ValueLabelNames :=
  wrappedArrayString "value_label_names" k.toNat 129

def variableLabels (k : typeK r) : ByteArrayParser VariableLabels := 
  wrappedArrayString "variable_labels" k.toNat 321 λ s => if s.startsWith "\x00" then "" else s.replace "\x00" ""

def characteristic (e : Byteorder) : ByteArrayParser Characteristic := wrapped "ch" do
  let _length ← read32 e
  let varname ← readString 129
  let charname ← readString 129
  let contents ← many readString'
  return ⟨varname, charname, contents⟩

def characteristics (e : Byteorder) : ByteArrayParser Characteristics := wrapped "characteristics" (many (characteristic e))

def observation (e : Byteorder) (k : typeK r) (ty : VariableType) : ByteArrayParser Observation := do
  let p : ByteArrayParser (ty.toLeanType) := match ty with
  | .str n => readString n.val
  | .strL => sorry
  | .double => read32 e |>.map uint32ToDouble
  | .float => read16 e |>.map uint16ToFloat
  | .long => read32 e
  | .int => read16 e
  | .byte => read8
  sorry

def data (e : Byteorder) (k : typeK r) (varTypes : VariableTypes) : ByteArrayParser Data := wrapped "data" do
  let mut obs := #[]
  for ty in varTypes do
    obs := obs.push (←observation k ty)
  return obs

def dta : ByteArrayParser Dta := do
  expectS "<stata_dta>"
  let header ← header
  let {k, byteorder := e, ..} := header
  let map ← map e
  let varTypes ← variableTypes k e
  let varnames ← varnames k
  let sortlist ← sortlist k e
  let formats ← formats k
  let valueLabelNames ← valueLabelNames k
  let variableLabels ← variableLabels k
  let characteristics ← characteristics e
  let data ← data e k varTypes
  -- expectS "</stata_dta>"
  return ⟨header, map, varTypes, varnames, sortlist, formats, valueLabelNames, variableLabels, characteristics, data⟩

end Dta