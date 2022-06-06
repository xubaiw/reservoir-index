import UsCourts.Defs
import UsCourts.Federal.Defs

def Alaska : State := {
  identifier := .alaska
  districts := [
    .undivisioned
        (stateOrTerritory := .alaska)
        (identifier := none)
        (counties := [])
        (holdsCourtIn := [
          "Anchorage", 
          "Fairbanks", 
          "Juneau", 
          "Ketchikan", 
          "Nome"
        ])
  ]
}