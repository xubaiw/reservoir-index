import UsCourts.Defs
import UsCourts.Federal.Defs

def Delaware : State := {
  identifier := .delaware
  districts := [
    .undivisioned
        (stateOrTerritory := .delaware)
        (identifier := none)
        (counties := [])
        (holdsCourtIn := [
          "Wilmington"
        ])
  ]
}

def DistrictOfDelaware : District := Delaware.districts.get ⟨0, by decide⟩
