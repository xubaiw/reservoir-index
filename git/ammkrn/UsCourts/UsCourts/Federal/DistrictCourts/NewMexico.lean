import UsCourts.Defs
import UsCourts.Federal.Defs

def NewMexico : State := {
  identifier := .newMexico
  districts := [
    .undivisioned
        (stateOrTerritory := .newMexico)
        (identifier := none)
        (counties := [])
        (holdsCourtIn := [
          "Albuquerque", 
          "Las Cruces", 
          "Las Vegas", 
          "Roswell", 
          "Santa Fe", 
          "Silver City"
        ])
  ]
}
