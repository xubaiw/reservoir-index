import Lean.Data.Json
import Timelib.NanoPrecision.TimeZone.Basic
import Timelib.NanoPrecision.DateTime.DateTime
import UsCourts.Defs

open Lean

inductive CircuitTag
| firstCircuit
| secondCircuit
| thirdCircuit
| fourthCircuit
| fifthCircuit
| sixthCircuit
| seventhCircuit
| eighthCircuit
| ninthCircuit
| tenthCircuit
| eleventhCircuit
| dcCircuit
| federalCircuit
deriving DecidableEq, Repr, ToJson, FromJson

instance : ToString CircuitTag where
  toString c := (unCamelCase <| elideNamespace <| reprStr c).map Char.toUpper

structure Division where
  name : String
  counties : List String
  holdsCourtIn : List String
  specialInclusions : List String := []
  specialExclusions : List String := []
  specialHoldsCourtIn : List String := []
deriving DecidableEq, Hashable, Repr, ToJson, FromJson

def Division.fullName (d : Division) : String :=
  s!"{d.name} DIVISION"

structure District where
  --timeOffset : Offset
  stateOrTerritory : StateOrTerritoryTag
  identifier : Option String
  divisions : List Division
  counties : List String
  holdsCourtIn : List String
  specialInclusions : List String := []
  specialExclusions : List String := []
  specialHoldsCourtIn : List String := []
deriving DecidableEq, Hashable, Repr, ToJson, FromJson

def District.timeOffset (d : District) : Offset := sorry
def District.timeZone (d : District) : TimeZone := d.timeOffset.toTimeZone
def District.observedNonstandardHolidays (d : District) : List Holiday := sorry

/- For rule 6 stuff. -/
def District.allRelevantHolidays (d : District) : List Holiday := 
  federalHolidays ++ d.observedNonstandardHolidays

--def District.clerksOfficeClosesAt (d : District) : ScalarDate → Option (DateTime d.timeOffset):= 
--  sorry
--
--def District.clerksOfficeInaccessible (d : District) (x : ScalarDate) (electronic : Bool) : Bool := 
--  sorry
--
--def District.firstAccessibleDayAfter (d : District) (x : ScalarDate) (electronic : Bool) : ScalarDate := 
--  sorry

def District.fullName (d : District) : String :=
  let pfx := ((d.identifier.map (fun i => s!"{i} ")).getD "").map Char.toUpper
  let mid := s!"DISTRICT OF {ToString.toString d.stateOrTerritory}"
  pfx ++ mid

def District.undivisioned 
  (stateOrTerritory : StateOrTerritoryTag)
  (counties : List String)
  (holdsCourtIn : List String)
  (identifier : Option String := none)
  (specialInclusions specialExclusions specialHoldsCourtIn : List String := []) : District :=
  {
    stateOrTerritory
    identifier
    divisions := []
    counties    
    holdsCourtIn
    specialInclusions
    specialExclusions
    specialHoldsCourtIn
  }

def District.divisioned
  (stateOrTerritory : StateOrTerritoryTag)
  (divisions : List Division) 
  (identifier : Option String := none) : District :=
  {
    stateOrTerritory
    identifier
    divisions
    counties := divisions.bind (fun d => d.counties)
    holdsCourtIn := divisions.bind (fun d => d.holdsCourtIn)
    specialInclusions := divisions.bind (fun d => d.specialInclusions)
    specialExclusions := divisions.bind (fun d => d.specialExclusions)
    specialHoldsCourtIn := divisions.bind (fun d => d.specialHoldsCourtIn)
  }

structure State where
  identifier : StateOrTerritoryTag
  districts : List District
deriving DecidableEq, Repr, ToJson, FromJson

def State.stateHolidays (s : State) : List Holiday := sorry

def StateOrTerritoryTag.stateHolidays (s : StateOrTerritoryTag) : List Holiday := sorry

structure Circuit where
  districts : List District
  locatedIn : StateOrTerritoryTag
