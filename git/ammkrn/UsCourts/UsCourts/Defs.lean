import Lean.Data.Json
import Timelib.Date.Year
import Timelib.Date.Month
import Timelib.Date.ScalarDate
import Timelib.Date.Basic
import Timelib.Date.Ymd

open Lean

structure Holiday where
  date : Year → ScalarDate

def mlkDay (y : Year) : ScalarDate := 
  y.nthKDayOfMonth 3 monday .january

def washingtonDay (y : Year) : ScalarDate := 
  y.nthKDayOfMonth 3 monday .february

def memorialDay (y : Year) : ScalarDate := 
  y.lastKDayOfMonth monday .may

def juneteenth (y : Year) : ScalarDate := 
  (Ymd.mk y .june 19 (by decide) (by simp [Month.numDays])).toScalarDate

def independenceDay (y : Year) : ScalarDate := 
  (Ymd.mk y .july 4 (by decide) (by simp [Month.numDays])).toScalarDate

def laborDay (y : Year) : ScalarDate := 
  y.firstKDayOfMonth monday .september

def columbusDay (y : Year) : ScalarDate := 
  y.nthKDayOfMonth 2 monday .october

def veteransDay (y : Year) : ScalarDate := 
  (Ymd.mk y .november 11 (by decide) (by simp [Month.numDays])).toScalarDate

def thanksgivingDay (y : Year) : ScalarDate := 
  y.nthKDayOfMonth 4 thursday .november

def christmasDay (y : Year) : ScalarDate := 
  (Ymd.mk y .december 25 (by decide) (by simp [Month.numDays])).toScalarDate

/- The base federal holidays defined by FRCP rule 6 -/
def baseFederalHolidays : List Holiday := [
  ⟨mlkDay⟩,
  ⟨washingtonDay⟩,
  ⟨memorialDay⟩,
  ⟨juneteenth⟩,
  ⟨independenceDay⟩,
  ⟨laborDay⟩,
  ⟨columbusDay⟩,
  ⟨veteransDay⟩,
  ⟨thanksgivingDay⟩,
  ⟨christmasDay⟩
]

def unCamelCase (s : String) : String := 
  s.foldl (fun sink next => sink ++ if next.isUpper then s!" {next}" else s!"{next}") ""
  
def elideNamespace (s : String) : String :=
  s.foldl (fun sink next => if next = '.' then "" else sink ++ s!"{next}") ""

inductive StateOrTerritoryTag
| alabama 
| alaska 
| arizona 
| arkansas 
| california 
| colorado 
| connecticut 
| delaware 
| florida 
| georgia 
| hawaii 
| idaho 
| illinois 
| indiana 
| iowa 
| kansas 
| kentucky 
| louisiana 
| maine 
| maryland 
| massachusetts 
| michigan 
| minnesota 
| mississippi 
| missouri 
| montana 
| nebraska 
| nevada 
| newHampshire 
| newJersey 
| newMexico 
| newYork 
| northCarolina 
| northDakota 
| ohio 
| oklahoma 
| oregon 
| pennsylvania 
| rhodeIsland 
| southCarolina 
| southDakota 
| tennessee 
| texas 
| utah 
| vermont 
| virginia 
| washington 
| westVirginia 
| wisconsin
| wyoming
| washingtonDc
| americanSamoa 
| guam 
| northernMarianaIslands 
| puertoRico 
| usVirginIslands
deriving DecidableEq, Hashable, Repr, ToJson, FromJson

@[reducible]
def StateOrTerritoryTag.isTerritory : StateOrTerritoryTag → Prop
| americanSamoa => True
| guam => True
| northernMarianaIslands => True
| usVirginIslands => True
| _ => False

@[reducible]
def StateOrTerritoryTag.isState (s : StateOrTerritoryTag) : Prop :=
  ¬s.isTerritory
  
instance : ToString StateOrTerritoryTag where
  toString d := (unCamelCase <| elideNamespace <| reprStr d).map Char.toUpper

inductive CourtSystemTag
| federal
| state
| extraterritorial
| international
| «local»
| tribal
| other
deriving DecidableEq, Repr, ToJson, FromJson

structure CourtSystem where
  system : CourtSystemTag
  notes : String
deriving DecidableEq, Repr, ToJson, FromJson

inductive CourtKindTag
| trial
| appellate
| bankruptcy
| ag
| other
deriving DecidableEq, Repr, ToJson, FromJson

structure CourtKind where
  kind : CourtKindTag
  notes : String
deriving DecidableEq, Repr, ToJson, FromJson

structure DateEntry where
  begin : Option Ymd
  beginNotes : Option String
  «end» : Option Ymd
  endNotes : Option String
deriving DecidableEq, Repr, ToJson, FromJson

structure Entry where
  name : String
  regex : List String
  citationString : String
  kind : List CourtKind
  system : CourtSystem
  sourceOfAuthority : Option String
  defunct : Bool
  dates : List DateEntry
  primaryLocation: String
  primaryLocationNotes: String
  numLocations : Option Nat
  courtUrl : String
  examples : List String
  id : Option String
  notes : List String
deriving DecidableEq, Repr, ToJson, FromJson
