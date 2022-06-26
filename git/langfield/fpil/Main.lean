import Fpil


-- Section 1.1

#eval 42 + 19 -- 61 : Nat
#eval String.append "A" (String.append "B" "C") -- "ABC" : String
#eval String.append (String.append "A" "B") "C" -- "ABC" : String
#eval if 3 == 3 then 5 else 7 -- 5 : Nat
#eval if 3 == 4 then "equal" else "not equal" -- "not equal" : String


-- Section 1.3

def joinStringsWith (sep : String) (a : String) (b : String) : String :=
  a ++ sep ++ b

#check joinStringsWith                          -- String → String → String → String
#eval joinStringsWith " " "a" "b"               -- "a b"
#eval joinStringsWith ", " "one" "and another"  -- "one, and another"
#check joinStringsWith ", "                     -- String → String → String

def vol (x : Nat) (y : Nat) (z : Nat) : Nat := x * y * z

#eval vol 1 2 3 -- 6


-- Section 1.4

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr

def samplePrism : RectangularPrism := {height := 1, width := 1, depth := 1}
#check samplePrism
#eval samplePrism

def nontrivialPrism : RectangularPrism := {height := 2, width := 3, depth := 4}
#check nontrivialPrism
#eval nontrivialPrism

-- Can we use a more expressive type that `Float`?
def badPrism : RectangularPrism := {height := -1, width := 1, depth := 1}
#check badPrism
#eval badPrism

def volume (prism : RectangularPrism) : Float :=
  prism.height * prism.width * prism.depth

#eval volume nontrivialPrism

structure Point where
  x : Float
  y : Float
deriving Repr

structure Segment where
  a : Point
  b : Point
deriving Repr

def length (s : Segment) : Float :=
  Float.sqrt (Float.pow dx 2 + Float.pow dy 2) where
    dx := s.b.x - s.a.x
    dy := s.b.y - s.a.y

def origin : Point := {x := 0, y := 0}
def p : Point := {x := 3, y := 5}

def s : Segment := Segment.mk origin p
#eval length s -- 5.830952
#eval Float.pow 5.830952 2

-- An n-dimensionl analogue of `Segment`.

inductive Vector (α : Type u) : Nat → Type u
  | nil : Vector α 0
  | cons : α → Vector α n → Vector α (n+1)
deriving Repr

#check Vector.cons 0 Vector.nil

def listToVector (xs : List α) : Vector α xs.length :=
  sorry

def vectorToList (v : Vector α n) : List α :=
  sorry

structure NSegment (n : Nat) where
  a : Vector Float n
  b : Vector Float n
deriving Repr

def nlength {n : Nat} (s : NSegment n) : Float :=
  sorry
  

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
