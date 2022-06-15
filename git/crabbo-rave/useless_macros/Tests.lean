import Macros

-- let macro

def test : Nat :=
  let y := 4
  let x := 3 in x+y

def test' : Nat :=
  let y := 4 in 
  let x := 3 in x + y

def test2 : Nat :=
  let x := 3, y := 4 in x + y


def test3 : List Nat :=
  let x := [1, 2], y := [3, 4] in x ++ y

#eval test -- 7
#eval test2 -- 7
#eval test3 -- [1, 2, 3, 4]

-- define 

def add(a : Nat, b : Nat) -> Nat: 
  a + b

def foo(a : Nat, b : Bool) -> Nat:
  a + if b then 1 else 0

def id'(α : Type, a : α) -> α: a

#eval add 1 5
#eval foo 7 true
#eval id' (List Nat) [1, 2, 3, 4]

-- c enums

enum direction {
  North,
  South,
  West,
  East,
  Other
};

instance : Repr direction where
  reprPrec
    | .North => reprPrec "North"
    | .South => reprPrec "South"
    | .East => reprPrec "East"
    | .West => reprPrec "West"
    | .Other => reprPrec "Somewhere In Between"

def getDirection : Nat → direction 
  | 0 => .North
  | 360 => .North 
  | 90 => .East 
  | 180 => .South 
  | 270 => .West 
  | _ => .Other

#eval getDirection 180
#eval getDirection 91