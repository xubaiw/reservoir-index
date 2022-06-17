import UsCourts.Defs
import UsCourts.Federal.Defs

def Ohio.NorthernDistrict.EasternDivision : Division := {
  name := "Eastern"
  counties := [
    "Ashland", 
    "Ashtabula", 
    "Carroll", 
    "Columbiana", 
    "Crawford", 
    "Cuyahoga", 
    "Geauga", 
    "Holmes", 
    "Lake", 
    "Lorain", 
    "Mahoning", 
    "Medina", 
    "Portage", 
    "Richland", 
    "Stark", 
    "Summit", 
    "Trumbull", 
    "Tuscarawas", 
    "Wayne"
  ]
  holdsCourtIn := [
    "Cleveland", 
    "Youngstown", 
    "Akron"
  ]
}

def Ohio.NorthernDistrict.WesternDivision : Division := {
  name := "Western"
  counties := [
    "Allen", 
    "Auglaize", 
    "Defiance", 
    "Erie", 
    "Fulton", 
    "Hancock", 
    "Hardin", 
    "Henry", 
    "Huron", 
    "Lucas", 
    "Marion", 
    "Mercer", 
    "Ottawa", 
    "Paulding", 
    "Putnam", 
    "Sandusky", 
    "Seneca", 
    "Van Wert", 
    "Williams", 
    "Woods", 
    "Wyandot"
  ]
  holdsCourtIn := [
    "Lima",
    "Toledo"
  ]
}

def Ohio.NorthernDistrict : District :=
  .divisioned
    (stateOrTerritory := .ohio)
    (identifier := "Northern")
    (divisions := [
      Ohio.NorthernDistrict.WesternDivision,
      Ohio.NorthernDistrict.EasternDivision
    ])

def Ohio.SouthernDistrict.EasternDivision : Division := {
  name := "Eastern"
  counties := [
    "Athens", 
    "Belmont", 
    "Coshocton", 
    "Delaware", 
    "Fairfield", 
    "Fayette", 
    "Franklin", 
    "Gallia", 
    "Guernsey", 
    "Harrison", 
    "Hocking", 
    "Jackson", 
    "Jefferson", 
    "Knox", 
    "Licking", 
    "Logan", 
    "Madison", 
    "Meigs", 
    "Monroe", 
    "Morgan", 
    "Morrow", 
    "Muskingum", 
    "Noble", 
    "Perry", 
    "Pickaway", 
    "Pike", 
    "Ross", 
    "Union", 
    "Vinton", 
    "Washington"
  ]
  holdsCourtIn := [
    "Columbus", 
    "St. Clairsville", 
    "Steubenville"
  ]
}

def Ohio.SouthernDistrict.WesternDivision : Division := {
  name := "Western"
  counties := [
    "Adams", 
    "Brown", 
    "Butler", 
    "Champaign", 
    "Clark", 
    "Clermont", 
    "Clinton", 
    "Darke", 
    "Greene", 
    "Hamilton", 
    "Highland", 
    "Lawrence", 
    "Miami", 
    "Montgomery", 
    "Preble", 
    "Scioto", 
    "Shelby", 
    "Warren"
  ]
  holdsCourtIn := [
    "Cincinnati",
    "Dayton"
  ]
}

def Ohio.SouthernDistrict: District :=
  .divisioned
    (stateOrTerritory := .ohio)
    (identifier := "Southern")
    (divisions := [
      Ohio.SouthernDistrict.WesternDivision,
      Ohio.SouthernDistrict.EasternDivision
    ])

def Ohio : State := {
  identifier := .ohio
  districts := [
    Ohio.NorthernDistrict,
    Ohio.SouthernDistrict
  ]
}
