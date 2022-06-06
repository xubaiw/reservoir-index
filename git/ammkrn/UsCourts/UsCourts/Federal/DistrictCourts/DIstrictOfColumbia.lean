import UsCourts.Defs
import UsCourts.Federal.Defs

def DistrictOfColumbia : District :=
  .undivisioned
      (stateOrTerritory := .washingtonDc)
      (identifier := "Columbia")
      (counties := [
      ])
      (holdsCourtIn := [
        "Washington"
      ])
