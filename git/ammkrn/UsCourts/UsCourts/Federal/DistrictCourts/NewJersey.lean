import UsCourts.Defs
import UsCourts.Federal.Defs

def NewJersey : State := {
  identifier := .newJersey
  districts := [
    .divisioned
        (stateOrTerritory := .newJersey)
        (identifier := none)
        (divisions := [
          {
            name := "Camden"
            counties := [
              "Atlantic", 
              "Burlington", 
              "Camden", 
              "Cape May", 
              "Cumberland", 
              "Gloucester", 
              "Salem"
            ]
            holdsCourtIn := []
          },
          {
            name := "Newark"
            counties := [
              "Bergen", 
              "Essex", 
              "Hudson", 
              "Morris", 
              "Passaic", 
              "Sussex", 
              "Union", 
              "Middlesex" 
            ]
            holdsCourtIn := []

          },
          {
            name := "Trenton"
            counties := [
              "Hunterdon", 
              "Mercer", 
              "Monmouth", 
              "Ocean", 
              "Somerset", 
              "Warren",
              "Middlesex"
            ]
            holdsCourtIn := []
          }
        ])
  ]
}

def DistrictOfNewJersey : District := NewJersey.districts.get ⟨0, by decide⟩
