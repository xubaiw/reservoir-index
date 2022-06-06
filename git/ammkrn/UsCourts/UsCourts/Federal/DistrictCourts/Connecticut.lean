import UsCourts.Defs
import UsCourts.Federal.Defs

def Connecticut : State := {
  identifier := .connecticut
  districts := [
    .undivisioned
        (stateOrTerritory := .connecticut)
        (identifier := none)
        (counties := [])
        (holdsCourtIn := [
          "Bridgeport", 
          "Hartford", 
          "New Haven", 
          "New London", 
          "Waterbury"
        ])
  ]
}

def DistrictOfConnecticut : District := Connecticut.districts.get ⟨0, by decide⟩

