import Dta.Basic
import Parsec

open Parsec ByteArrayParser

namespace Dta

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

def header : ByteArrayParser Header := do
  expectS "<header>"
  expectS "<release>"
  let r ← release
  expectS "</release>"
  expectS "<byteorder>"
  let e ← byteorder
  expectS "</byteorder>"
  expectS "<K>"
  let k ← k r e
  expectS "</K>"
  expectS "<N>"
  let n ← n e
  expectS "</N>"
  expectS "<label>"
  let label ← label e
  expectS "</label>"
  expectS "<timestamp>"
  let timestamp? ← timestamp?
  expectS "</timestamp>"
  expectS "</header>"
  return ⟨r, e, k, n, label, timestamp?⟩

def map (e : Byteorder) : ByteArrayParser Map := do
  expectS "<map>"
  let map ← readArray 14 <| read64 e
  expectS "</map>"
  return map

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

-- def readBytes (sz : Nat) : ByteArrayParser ByteArray := do
--   let pos ← get
--   let ba ← read
--   if pos + sz <= ba.size then
--     (pure <| ba.extract pos (pos + sz)) <* modify (· + sz)
--   else
--     error s!"eof before {sz} bytes"

def varname : ByteArrayParser String := do
  let s ← readString 129
  return s.replace "\x00" ""

def varnames (k : typeK r) : ByteArrayParser VarNames := do
  expectS "<varnames>"
  let varnames ← readArray k.toNat varname
  expectS "</varnames>"
  return varnames

def dta : ByteArrayParser Dta := do
  expectS "<stata_dta>"
  let header ← header
  let map ← map header.byteorder
  let varTypes ← variableTypes header.k header.byteorder
  let varnames ← varnames header.k
  -- expectS "</stata_dta>"
  return ⟨header, map, varTypes, varnames⟩

end Dta