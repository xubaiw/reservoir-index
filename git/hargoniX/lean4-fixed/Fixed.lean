/-
  Copyright (c) 2021 Henrik Böving. All rights reserved.
  Released under MIT license as described in the file LICENSE.
  Authors: Henrik Böving
-/

/--
  Fixed n represents a fixed precision number with resolution n.
  For example n = 10 can calculate with 1 digit after comma, n=100 with
  2 and so on.
-/
structure Fixed (resolution : Nat) where
  (val : Int)
  deriving Inhabited, BEq, DecidableEq, Repr, Ord
-- TODO: Implement a nice ToString instance

abbrev Uni := Fixed 1
abbrev Deci := Fixed 10
abbrev Centi := Fixed 100
abbrev Milli := Fixed 1000
abbrev Micro := Fixed 1000000
abbrev Nano := Fixed 1000000000
abbrev Pico := Fixed 1000000000000

namespace Fixed

def add : Fixed n → Fixed n → Fixed n
| a, b => Fixed.mk $ a.val + b.val

def sub : Fixed n → Fixed n → Fixed n
| a, b => Fixed.mk $ a.val - b.val

def neg : Fixed n → Fixed n
| a => Fixed.mk $ -(a.val)

def mul : Fixed n → Fixed n → Fixed n
| a, b => Fixed.mk $ (a.val * b.val) / n

def div : Fixed n → Fixed n → Fixed n
| a, b => Fixed.mk $ (a.val * n) / b.val

/- 1 as Int is interpreted as a whole so 1.0 -/
def ofInt (m : Int) : Fixed n := Fixed.mk $ n * m

/- 1.0 is interpreted as a whole. Since it's scientific notation this
   implicitly assumes that n is a base 10 number to convert. -/
def ofScientific : Nat → Bool → Nat → Fixed n
| m, true, e => Fixed.mk $ m * (n / (10^e : Nat))
| m, false, e => Fixed.mk $ m * (10^e : Nat) * n

instance : Add (Fixed n) := ⟨add⟩
instance : Sub (Fixed n) := ⟨sub⟩
instance : Mul (Fixed n) := ⟨mul⟩
instance : Div (Fixed n) := ⟨div⟩
instance : Neg (Fixed n) := ⟨neg⟩
instance : LT (Fixed n) := ltOfOrd
instance : LE (Fixed n) := leOfOrd

instance : OfNat (Fixed n) m where
  ofNat := ofInt m

instance : OfScientific (Fixed n) where
  ofScientific := ofScientific

def toFloat : Fixed n → Float
| a => (Float.ofInt a.val) / (Float.ofNat n)

def nextMetricLevel : Fixed n → Fixed (n * 10)
|  a => Fixed.mk $ a.val * 100

end Fixed
