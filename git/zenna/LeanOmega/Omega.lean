import Mathlib
import Lean

-- constants
constant m : Nat := (2^16+1)

-- shrink x to the unit interval --
def shrink x := (Nat.toFloat x) / m.toFloat

-- Logistic sequence
def next_rand r := (75*r + 74)%(2^16+1)

-- nth element of the random sequence
def nth_rand : Nat → Nat 
| 0    => next_rand 0
| (n+1) => next_rand (nth_rand n)


def nth_rand_seeded seed n :=
  match n with 
  | 0    => next_rand seed
  | (n+1) => next_rand (nth_rand_seeded seed n)

def ω_seeded seed := shrink ∘ (nth_rand_seeded seed)

-- def ω := f ∘ nth_rand
-- A class is a sequence of random variables, indexed by their id
def std_uniform_class (id: Nat) (ω_: Nat → Float) := ω_ id
def logistic_quantile μ_ s_ p := μ_ + s_ * Float.log (p / (1 - p))
def logistic μ s := (λ id ω => (logistic_quantile μ s (std_uniform_class id ω)))

-- Fundamentals
def Ω := Nat → Float

-- τ-valued random variable
def RV (τ : Type u) := Ω → τ

-- Inductive type to value or nothing
inductive Value (τ : Type)
| value : τ → Value τ
| nothing

open Value

-- Conditional random variable
def condition {τ : Type} (x : RV τ) (y : RV Bool) : (RV (Value τ)) := λ ω => if (y ω) then (value (x ω)) else nothing

-- class Unconditioend

def rejection_sample_simple {τ : Type} (x : RV τ) seed := x (ω_seeded seed)

-- Keep sampling from x until its conditions are true
partial def rejection_sample {τ : Type} [Inhabited τ] (x : RV (Value τ)) (seed : ℕ) : τ :=
  let x_ := x (ω_seeded seed)
  match x_ with
  | nothing => rejection_sample x (seed + 1)
  | value v => v


def pwAdd {τ : Type u} [Add τ] (x : RV τ) (y : RV τ) := λ ω => x ω + y ω

def pw {α β γ : Type u} (f : α → β → γ) (x : RV α) (y : RV β) := λ ω => f (x ω) (y ω)

-- Add random variable as instance to Add, defined pointwise
-- instance : Add (RV Float) where
--   add := pwAdd

-- instance [Add α] [Add β] : Add {α : Type u} {β : Type v}  where
--   add (α × β) := ⟨λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => ⟨a₁+a₂, b₁+b₂⟩⟩

def f (x : Float) := x * x

instanceof 

variable {vv}
instance {α : Type u} {β : Type v} [Add β] : Add (α → β) where
  add := λ f g x => Add.add (f x) (g x)

instance {α : Type u} {β : Type v} [LT β] : LT (α → β) where
  lt := λ f g x => (f x) > (g x)



-- #print Add

-- instance {α : Type u} {β : Type v} {γ : Type v} : Prod (α → β) (α → γ) where
--   mk := λ f g x => Prod.mk (f x) (g x)

-- instance : HAdd (RV Float) (RV Float) where
--   hAdd := pwAdd

-- Model
def x := std_uniform_class 1
def y := std_uniform_class 2

def xy := x + y

#eval rejection_sample_simple (x + x + x) 3

def a : ℕ := 3
def c : ℕ := 4
def q := Nat.le a c
#print Set

def z := x + y
def joint ω := (x ω, y ω, z ω)
def z_ := z > x
LT.lt
def z_is_pos_condition (ω : Ω) : Bool
  := ((z ω) > 1)

def joint_posterior := condition x z_is_pos_condition
def squeeze_x_condition (ω : Ω) : Bool
  := ((x ω) > 0.99)

-- #check (condition joint z_is_pos_condition)
#eval rejection_sample (condition x squeeze_x_condition) 1
-- #eval rejection_sample (condition x z_is_pos_condition) 4
-- #eval rejection_sample (condition x squeeze_x_condition) 8576


-- #xamples
#check Add.add x x
#check 2 3

-- Pointwise is very tricky/impossile 
