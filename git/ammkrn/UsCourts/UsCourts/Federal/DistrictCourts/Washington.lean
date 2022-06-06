import UsCourts.Defs
import UsCourts.Federal.Defs

def Washington.EasternDistrict : District := 
  .undivisioned
  (stateOrTerritory := .washington)
  (identifier := "Eastern")
  (counties := [
    "Adams", 
    "Asotin", 
    "Benton", 
    "Chelan", 
    "Columbia", 
    "Douglas", 
    "Ferry", 
    "Franklin", 
    "Garfield", 
    "Grant", 
    "Kittitas", 
    "Klickitat", 
    "Lincoln", 
    "Okanogan", 
    "Pend Oreille", 
    "Spokane", 
    "Stevens", 
    "Walla Walla", 
    "Whitman", 
    "Yakima"
  ])
  (holdsCourtIn := [
    "Spokane",
    "Yakima",
    "Walla Walla",
    "Richland"
  ])

def Washington.WesternDistrict : District :=
  .undivisioned
    (stateOrTerritory := .washington)
    (identifier := "Western")
    (counties := [
      "Clallam", 
      "Clark", 
      "Cowlitz", 
      "Grays Harbor", 
      "Island", 
      "Jefferson", 
      "King", 
      "Kitsap", 
      "Lewis", 
      "Mason", 
      "Pacific", 
      "Pierce", 
      "San Juan", 
      "Skagit", 
      "Skamania", 
      "Snohomish", 
      "Thurston", 
      "Wahkiakum", 
      "Whatcomnone"
    ])
    (holdsCourtIn := [
      "Bellingham",
      "Seattle",
      "Tacoma",
      "Vancouver" 
    ])

def Washington : State := {
  identifier := .washington
  districts := [
    Washington.EasternDistrict, 
    Washington.WesternDistrict
  ]
}

