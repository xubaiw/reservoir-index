import Dta.Basic
import Parsec

open Parsec Binary Parser

namespace Dta

def wrapped (tag : String) (p : Parser α) : Parser α := do
  expectS s!"<{tag}>"
  let s ← p
  expectS s!"</{tag}>"
  return s

def wrappedArray (tag : String) (num : Nat) (p : Parser α) : Parser (Array α) := do
  wrapped tag (readArray num p)

def wrappedArrayString (tag : String) (num length : Nat) (f : String → String := (·.replace "\x00" "")) : Parser (Array String) := do
  wrappedArray tag num s
where
  s := do
    let s ← readString length
    return f s

@[inline]
partial def manyCore (p : Parser α) (acc : Array α) : Parser (Array α) := do
  try
    let res ← p
    manyCore p (acc.push res)
  catch _ =>
    return acc

@[inline]
def many (p : Parser α) : Parser $ Array α := manyCore p #[]

partial def readString' : Parser String := do
  let mut arr := ByteArray.empty
  repeat do
    let s ← peek
    if s = 0 then
      break
    arr := arr.push s
  return arr |> String.fromUTF8Unchecked

def release : Parser Release := do
  match ←readString 3 with
  | "113" => return .«113»
  | "114" => return .«114»
  | "115" => return .«115»
  | "117" => return .«117»
  | "118" => return .«118»
  | "119" => return .«119»
  | _     => fail "invalid <release> field"

def byteorder : Parser Byteorder := do
  match ←readString 3 with
  | "LSF" => return .lsf
  | "MSF" => return .msf
  | _      => fail "invalid <byteorder> field"

def read16 : Byteorder → Parser UInt16
| .lsf => read16LE
| .msf => read16BE

def read32 : Byteorder → Parser UInt32
| .lsf => read32LE
| .msf => read32BE

def read48 (bo : Byteorder) : Parser UInt64 := do
  let a ← read8
  let b ← read8
  let c ← read8
  let d ← read8
  let e ← read8
  let f ← read8 
  return match bo with
  | .lsf => a.toUInt64 ||| (b.toUInt64 <<< 8) ||| (c.toUInt64 <<< 16) ||| (d.toUInt64 <<< 24) ||| (e.toUInt64 <<< 32) ||| (f.toUInt64 <<< 40)
  | .msf => f.toUInt64 ||| (e.toUInt64 <<< 8) ||| (d.toUInt64 <<< 16) ||| (c.toUInt64 <<< 24) ||| (b.toUInt64 <<< 32) ||| (a.toUInt64 <<< 40)

def read64 : Byteorder → Parser UInt64
| .lsf => read64LE
| .msf => read64BE

def readFloat : Byteorder → Parser Float
| .lsf => readFloatLE
| .msf => readFloatBE

def readDouble : Byteorder → Parser Float
| .lsf => readDoubleLE
| .msf => readDoubleBE

def k (r : Release) (e : Byteorder) : Parser (typeK r) := by
  cases r <;> simp [typeK]
  repeat exact read16 e
  exact read32 e

def n (e : Byteorder) := read64 e

def label (e : Byteorder) : Parser String := do
  let length ← read16 e
  readString length.toNat

def timestamp? : Parser (Option String) := do
  let length ← read8
  match length with
  |  0 => return none
  | 17 => return (←readString 17)
  |  _ => fail "length of timestamp must be 0 or 17"

def header : Parser Header := wrapped "header" do
  let r ← wrapped "release" release
  let e ← wrapped "byteorder" byteorder
  let k ← wrapped "K" (k r e)
  let n ← wrapped "N" (n e)
  let label ← wrapped "label" (label e)
  let timestamp? ← wrapped "timestamp" timestamp?
  return ⟨r, e, k, n, label, timestamp?⟩

def map (e : Byteorder) : Parser Map := do
  wrappedArray "map" 14 (read64 e)

def variableTypes (k : typeK r) (e : Byteorder) : Parser VariableTypes := do
  expectS "<variable_types>"
  let mut arr := #[]
  for x in ←readArray k.toNat (read16 e) do
    match x with
    | 32768 => arr := arr.push .strLIndex
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
        throw (←fail "variable type out of range")
  expectS "</variable_types>"
  return arr

def varnames (k : typeK r) : Parser VarNames :=
  wrappedArrayString "varnames" k.toNat 129

def sortlist (k : typeK r) (e : Byteorder) : Parser SortList := do
  wrappedArray "sortlist" (k.toNat + 1) (read16 e)

def formats (k : typeK r) : Parser Formats :=
  wrappedArrayString "formats" k.toNat 57

def valueLabelNames (k : typeK r) : Parser ValueLabelNames :=
  wrappedArrayString "value_label_names" k.toNat 129

def variableLabels (k : typeK r) : Parser VariableLabels := 
  wrappedArrayString "variable_labels" k.toNat 321 λ s => if s.startsWith "\x00" then "" else s.replace "\x00" ""

def characteristic (e : Byteorder) : Parser Characteristic := wrapped "ch" do
  let length ← read32 e
  let varname ← readString 129
  let charname ← readString 129
  let contents ← readString (length.toNat - 258)
  return ⟨varname, charname, contents⟩

def characteristics (e : Byteorder) : Parser Characteristics := wrapped "characteristics" (many (characteristic e))

def readStrlIndex (e : Byteorder) : Parser (UInt32 × UInt64) := do
  let a ← read16 e <&> UInt16.toUInt32
  let b ← read48 e
  return (a, b)

def value (e : Byteorder) (ty : VariableType) : Parser Value :=
  match ty with
  | .str n => readString n.val <&> Value.str n
  | .strLIndex => readStrlIndex e <&> Value.strLIndex
  | .double => readDouble e <&> Value.double
  | .float => readFloat e <&> Value.float
  | .long => read32 e <&> Value.long
  | .int => read16 e <&> Value.int
  | .byte => read8 <&> Value.byte

def observation (e : Byteorder) (tys : VariableTypes) : Parser Observation := do
  let mut arr := #[]
  for ty in tys do
    let v ← value e ty
    arr := arr.push v
  return arr

def data (e : Byteorder) (n : UInt64) (tys : VariableTypes) : Parser Data :=
  wrappedArray "data" n.toNat (observation e tys)

def gso (e : Byteorder) : Parser GSO := do
  expectS "GSO" 
  let v ← read32 e
  let o ← read64 e
  let t ← read8
  let len ← read32 e
  match t with
  | 129 => 
    let content ← readString len.toNat
    return ⟨v, o, true, len, content⟩
  | 130 => 
    let content ← readString'
    return ⟨v, o, true, len, content⟩
  | _ => throw (←fail s!"t must be 129 (binary) or 130 (ascii), but got {t}")

def strLs (e : Byteorder) : Parser StrLs :=
  wrapped "strls" <| many <| gso e

def dta : Parser Dta := do
  expectS "<stata_dta>"
  let header ← header
  let {k, n, byteorder := e, ..} := header
  let map ← map e
  let varTypes ← variableTypes k e
  let varnames ← varnames k
  dbg_trace "varnames"
  dbg_trace repr varnames
  let sortlist ← sortlist k e
  dbg_trace "sortlist"
  dbg_trace sortlist
  let formats ← formats k
  dbg_trace "format"
  dbg_trace formats
  let valueLabelNames ← valueLabelNames k
  dbg_trace "valueLabe"
  dbg_trace valueLabelNames
  let variableLabels ← variableLabels k
  dbg_trace "varLabel"
  dbg_trace variableLabels
  let characteristics ← characteristics e
  dbg_trace "charac"
  dbg_trace repr characteristics
  let data ← data e n varTypes
  dbg_trace "data"
  dbg_trace repr data
  let strLs ← strLs e
  dbg_trace "strls"
  dbg_trace repr strLs
  expectS "</stata_dta>"
  return ⟨header, map, varTypes, varnames, sortlist, formats, valueLabelNames, variableLabels, characteristics, data, strLs⟩

end Dta
