import UsCourts.Defs
import UsCourts.Federal.Defs

def Michigan.EasternDistrict.NorthernDivision : Division := {
  name := "Northern"
  counties := [
    "Alcona", 
    "Alpena", 
    "Arenac", 
    "Bay", 
    "Cheboygan", 
    "Clare", 
    "Crawford", 
    "Gladwin", 
    "Gratiot", 
    "Huron", 
    "Iosco", 
    "Isabella", 
    "Midland", 
    "Montmorency", 
    "Ogemaw", 
    "Oscoda", 
    "Otsego", 
    "Presque Isle", 
    "Roscommon", 
    "Saginaw",
    "Tuscola"
  ]
  holdsCourtIn := [
    "Bay City"
  ]
}

def Michigan.EasternDistrict.SouthernDivision : Division := {
  name := "Southern"
  counties := [
    "Genesee", 
    "Jackson", 
    "Lapeer", 
    "Lenawee", 
    "Livingston", 
    "Macomb", 
    "Monroe", 
    "Oakland", 
    "Saint Clair", 
    "Sanilac", 
    "Shiawassee", 
    "Washtenaw", 
    "Wayne"
  ]
  holdsCourtIn := [
    "Ann Arbor", 
    "Detroit", 
    "Flint", 
    "Port Huron"
  ]
}

def Michigan.EasternDistrict : District := 
  .divisioned
    (stateOrTerritory := .michigan)
    (identifier := "Eastern")
    (divisions := [
      Michigan.EasternDistrict.NorthernDivision,
      Michigan.EasternDistrict.SouthernDivision
    ])

def Michigan.WesternDistrict.NorthernDivision : Division := {
  name := "Northern"
  counties := [
    "Alger", 
    "Baraga", 
    "Chippewa", 
    "Delta", 
    "Dickinson", 
    "Gogebic", 
    "Houghton", 
    "Iron", 
    "Keweenaw", 
    "Luce", 
    "Mackinac", 
    "Marquette", 
    "Menominee", 
    "Ontonagon",
    "Schoolcraft"
  ]
  holdsCourtIn := [
    "Marquette", 
    "Sault Sainte Marie"
  ]
}

def Michigan.WesternDistrict.SouthernDivision : Division := {
  name := "Southern"
  counties := [
    "Allegan", 
    "Antrim", 
    "Barry", 
    "Benzie", 
    "Berrien", 
    "Branch", 
    "Calhoun", 
    "Cass", 
    "Charlevoix", 
    "Clinton", 
    "Eaton", 
    "Emmet", 
    "Grand Traverse", 
    "Hillsdale", 
    "Ingham", 
    "Ionia", 
    "Kalamazoo", 
    "Kalkaska", 
    "Kent", 
    "Lake", 
    "Leelanau", 
    "Manistee", 
    "Mason", 
    "Mecosta", 
    "Missaukee", 
    "Montcalm", 
    "Muskegon", 
    "Newaygo", 
    "Oceana", 
    "Osceola", 
    "Ottawa", 
    "Saint Joseph", 
    "Van Buren",
    "Wexford"
  ]
  holdsCourtIn := [
    "Grand Rapids",
    "Kalamazoo", 
    "Lansing",
    "Traverse City"
  ]
}
def Michigan.WesternDistrict : District := 
  .divisioned
    (stateOrTerritory := .michigan)
    (identifier := "Western")
    (divisions := [
      Michigan.WesternDistrict.NorthernDivision,
      Michigan.WesternDistrict.SouthernDivision
    ])

abbrev EasternDistrictOfMichigan := Michigan.EasternDistrict
abbrev WesternDistrictOfMichigan := Michigan.WesternDistrict
    
def Michigan : State := {
  identifier := .michigan
  districts := [
    Michigan.EasternDistrict,
    Michigan.WesternDistrict
  ]
}

