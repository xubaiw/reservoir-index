import UsCourts.Defs
import UsCourts.Federal.Defs

def NewYork.NorthernDistrict : District := 
  .undivisioned
    (stateOrTerritory := .newYork)
    (identifier := "Northern")
    (counties := [
      "Albany", 
      "Broome", 
      "Cayuga", 
      "Chenango", 
      "Clinton", 
      "Columbia", 
      "Cortland", 
      "Delaware", 
      "Essex", 
      "Franklin", 
      "Fulton", 
      "Greene", 
      "Hamilton", 
      "Herkimer", 
      "Jefferson", 
      "Lewis", 
      "Madison", 
      "Montgomery", 
      "Oneida", 
      "Onondaga", 
      "Oswego", 
      "Otsego", 
      "Rensselaer", 
      "Saint Lawrence", 
      "Saratoga", 
      "Schenectady", 
      "Schoharie", 
      "Tioga", 
      "Tompkins", 
      "Ulster", 
      "Warren", 
      "Washington"
    ])
    /-
    Plattsburgh appears twice in the original law.
    -/
    (holdsCourtIn := [
      "Albany", 
      "Auburn", 
      "Binghamton", 
      "Malone", 
      "Plattsburgh",
      "Syracuse", 
      "Utica", 
      "Watertown"
    ])

def NewYork.SouthernDistrict : District := 
  .undivisioned
    (stateOrTerritory := .newYork)
    (identifier := "Southern")
    (counties := [
      "Bronx", 
      "Dutchess", 
      "New York", 
      "Orange", 
      "Putnam", 
      "Rockland", 
      "Sullivan", 
      "Westchester" 
    ])
    (holdsCourtIn := [
      "New York", 
      "White Plains"
    ])
    (specialInclusions := [
      "the Middletown-Wallkill area of Orange County or such nearby location as may be deemed appropriate"
    ])
    (specialHoldsCourtIn :=[
      "concurrently with the Eastern District, the waters within the Eastern District"
    ])

def NewYork.EasternDistrict : District :=
  .undivisioned
    (stateOrTerritory := .newYork)
    (identifier := "Eastern")
    (counties := [
      "Kings", 
      "Nassau", 
      "Queens", 
      "Richmond", 
      "Suffolk" 
    ])
    (specialInclusions := [
      "concurrently with the Southern District, the waters within the counties of Bronx and New York"
    ])
    (holdsCourtIn := [
      "Brooklyn", 
      "Hauppauge", 
      "Hempstead",
      "Central Islip"
    ])
    (specialHoldsCourtIn := [
      "the village of Uniondale"
    ])


def NewYork.WesternDistrict : District := 
  .undivisioned
    (stateOrTerritory := .newYork)
    (identifier := "Western")
    (counties := [
      "Allegany", 
      "Cattaraugus", 
      "Chautauqua", 
      "Chemung", 
      "Erie", 
      "Genesee", 
      "Livingston", 
      "Monroe", 
      "Niagara", 
      "Ontario", 
      "Orleans", 
      "Schuyler", 
      "Seneca", 
      "Steuben", 
      "Wayne", 
      "Wyoming",
      "Yates"
    ])
    (holdsCourtIn := [
      "Buffalo", 
      "Canandaigua", 
      "Elmira", 
      "Jamestown", 
      "Rochester"
    ])

def NewYork : State := {
  identifier := .newYork
  districts := [
    NewYork.NorthernDistrict,
    NewYork.SouthernDistrict,
    NewYork.EasternDistrict,
    NewYork.WesternDistrict
  ]
}