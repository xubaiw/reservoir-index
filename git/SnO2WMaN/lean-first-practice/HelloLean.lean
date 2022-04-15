namespace BasicFunctions

#eval 2+2

def sampleFuct1 x := x*x + 3
def result1 := sampleFuct1 50
#eval println! "Result1: {result1}"

def sampleFunc2 (x:Nat) := 2*x*x - x+3
def result2 := sampleFunc2 (11)
#eval println! "Result2: {result2}"

def sampleFunction3 (x : Nat) :=
  if x > 100 then
    2 * x * x - x + 3
  else
    2 * x * x + x - 37
#eval println! "Result3: {sampleFunction3 3}"

end BasicFunctions

def twice (f : Nat → Nat) (a : Nat) := f (f a)
theorem twiceAdd2 (a : Nat) : twice (fun x => x + 2) a = a + 4 :=
  rfl

--
#eval twice (· + 2) 10


inductive Weekday where
  | sunday    : Weekday
  | monday    : Weekday
  | tuesday   : Weekday
  | wednesday : Weekday
  | thursday  : Weekday
  | friday    : Weekday
  | saturday  : Weekday

#check Weekday.sunday
#check Weekday.monday

open Weekday
#check sunday
#check tuesday

def natOfWeekday (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7
#eval natOfWeekday monday


def Weekday.isMonday : Weekday → Bool :=
  fun
    | monday => true
    | _      => false

#eval isMonday sunday
#eval isMonday monday

instance: ToString Weekday where
  toString (d:Weekday):String :=
    match d with
      | sunday => "Sunday"
      | monday => "Monday"
      | tuesday => "Tuesday"
      | wednesday => "Wednesday"
      | thursday => "Thursday"
      | friday => "Friday"
      | saturday => "Saturday"

def Weekday.next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def Weekday.previous : Weekday -> Weekday
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval Weekday.next Weekday.wednesday
#eval next wednesday
#eval next (previous wednesday)

theorem Weekday.nextOfPrevious (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

theorem Weekday.nextOfPrevious' (d : Weekday) : next (previous d) = d := by
  cases d       -- A proof by case distinction
  all_goals rfl  -- Each case is solved using `rfl`

def hello := "world"