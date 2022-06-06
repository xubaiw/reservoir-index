import UsCourts.Defs
import UsCourts.Federal.Defs

def Illinois.NorthernDistrict.EasternDivision : Division := {
  name := "Eastern"
  counties := [
    "Cook", 
    "Du Page", 
    "Grundy", 
    "Kane", 
    "Kendall", 
    "Lake", 
    "La Salle", 
    "Will"
  ]
  holdsCourtIn := [
    "Chicago",
    "Wheaton"
  ]
}

def Illinois.NorthernDistrict.WesternDivision : Division := {
  name := "Western"
  counties := [
    "Boone", 
    "Carroll", 
    "De Kalb", 
    "Jo Daviess", 
    "Lee", 
    "McHenry", 
    "Ogle", 
    "Stephenson", 
    "Whiteside", 
    "Winnebago"
  ]
  holdsCourtIn := [
    "Freeport",
    "Rockford"
  ]
}

def Illinois.NorthernDistrict : District :=
  .divisioned
    (stateOrTerritory := .illinois)
    (identifier := "Northern")
    (divisions := [
      Illinois.NorthernDistrict.WesternDivision,
      Illinois.NorthernDistrict.EasternDivision
    ])
    

def Illinois.CentralDistrict : District :=
  .undivisioned
      (stateOrTerritory := .illinois)
      (identifier := "Central")
      (counties := [
        "Adams",
        "Brown",
        "Bureau",
        "Cass",
        "Champaign",
        "Christian",
        "Coles",
        "De Witt",
        "Douglas",
        "Edgar",
        "Ford",
        "Fulton",
        "Greene",
        "Hancock",
        "Henderson",
        "Henry",
        "Iroquois",
        "Kankakee",
        "Knox",
        "Livingston",
        "Logan", 
        "McDonough", 
        "McLean", 
        "Macoupin", 
        "Macon", 
        "Marshall", 
        "Mason", 
        "Menard", 
        "Mercer", 
        "Montgomery", 
        "Morgan", 
        "Moultrie", 
        "Peoria", 
        "Piatt", 
        "Pike", 
        "Putnam", 
        "Rock Island", 
        "Sangamon", 
        "Schuyler", 
        "Scott", 
        "Shelby", 
        "Stark", 
        "Tazewell", 
        "Vermilion", 
        "Warren",
        "Woodford"
      ])
      (holdsCourtIn := [
        "Champaign/Urbana",
        "Danville", 
        "Peoria", 
        "Quincy", 
        "Rock Island", 
        "Springfield"
      ])

def Illinois.SouthernDistrict : District :=
  .undivisioned
      (stateOrTerritory := .illinois)
      (identifier := "Southern")
      (counties := [
        "Alexander", 
        "Bond", 
        "Calhoun", 
        "Clark", 
        "Clay", 
        "Clinton", 
        "Crawford", 
        "Cumberland", 
        "Edwards", 
        "Effingham", 
        "Fayette", 
        "Franklin", 
        "Gallatin", 
        "Hamilton", 
        "Hardin", 
        "Jackson", 
        "Jasper", 
        "Jefferson", 
        "Jersey", 
        "Johnson", 
        "Lawrence", 
        "Madison", 
        "Marion", 
        "Massac", 
        "Monroe", 
        "Perry", 
        "Pope", 
        "Pulaski", 
        "Randolph", 
        "Richland", 
        "St. Clair", 
        "Saline", 
        "Union", 
        "Wabash", 
        "Washington", 
        "Wayne", 
        "White", 
        "Williamson"
      ])
      (holdsCourtIn := [
        "Alton",
        "Benton",
        "Cairo",
        "East Saint Louis"
      ])

def Illinois : State := {
  identifier := .illinois
  districts := [
    Illinois.NorthernDistrict,
    Illinois.CentralDistrict,
    Illinois.SouthernDistrict
  ]
}
