/- The com Language -/
namespace While

abbrev Map (α β : Type) := α → Option β

namespace Map

def empty : Map α β := λ _ => none

def update [DecidableEq α] (m : Map α β) (k : α) (v : Option β) : Map α β :=
  λ k' => if k = k' then v else m k'

scoped notation:max m "[" k " ↦ " v "]" => update m k v

end Map

/- Variables and Values -/

/-- names for variables -/
abbrev VName := String

inductive Ty where
  | int | bool
  deriving DecidableEq

inductive Val : Ty → Type where
  | bool (b : Bool) : Val Ty.bool
  | int  (i : Int)  : Val Ty.int
  deriving DecidableEq

-- lets us use a `Bool/Int` where a `Val` is expected
instance : Coe Bool (Val Ty.bool) := ⟨Val.bool⟩
instance : Coe Int  (Val Ty.int)  := ⟨Val.int⟩

/- Expressions and Commands -/

abbrev Ctxt := Map VName Ty

/-- binary operations -/
inductive BinOp : Ty → Ty → Type where
  | eq  : BinOp τ     .bool
  | and : BinOp .bool .bool
  | lt  : BinOp .int  .bool
  | add : BinOp .int  .int
  | sub : BinOp .int  .int

inductive Expr : Ctxt → Ty → Type where
  | const (v : Val τ) : Expr Γ τ
  | var (x : VName) (h : Γ x = some τ) : Expr Γ τ
  | binop (l : Expr Γ α) (op : BinOp α β) (r : Expr Γ α) : Expr Γ β

instance : Coe (Val τ) (Expr Γ τ) := ⟨Expr.const⟩

def BinOp.eval : BinOp α β → Val α → Val α → Val β
  | BinOp.eq,        v₁,       v₂ => Val.bool (v₁ = v₂)
  | BinOp.and, .bool b₁, .bool b₂ => Val.bool (b₁ ∧ b₂)
  | BinOp.lt,  .int  i₁, .int  i₂ => Val.bool (i₁ < i₂)
  | BinOp.add, .int  i₁, .int  i₂ => Val.int  (i₁ + i₂)
  | BinOp.sub, .int  i₁, .int  i₂ => Val.int  (i₁ - i₂)

inductive Com (Γ : Ctxt) where
  | skip
  | ass (x : VName) (e : Expr Γ τ) (h : Γ x = some τ)
  | seq (c c' : Com Γ)
  | cond (b : Expr Γ Ty.bool) (cₜ cₑ : Com Γ)
  | «while» (b : Expr Γ Ty.bool) (c : Com Γ)

theorem Expr.bool_rec (p : Expr Γ Ty.bool → Prop)
    (htrue : p true) (hfalse : p false) (hvar : ∀ x h, p (Expr.var x h))
    (hbinop : ∀ α l op r, p (@Expr.binop _ α _ l op r)) : ∀ x, p x
  | true | false | .var .. | .binop .. => by simp_all


infixr:130 ";; "  => Com.seq

/- Prettier embedding of `Expr` and `Com` as term-level macros -/
/- (You can ignore this part, jump to the examples below to see its usage) -/

open Lean
open Map

syntax "`[Expr|" term "]" : term

macro_rules
  | `(`[Expr|true])     => `((true : Expr _ Ty.bool))
  | `(`[Expr|false])    => `((false : Expr _ Ty.bool))
  | `(`[Expr|$n:num])   => `((($n : Nat) : Expr _ Ty.int))
  | `(`[Expr|$x:ident]) => `((Expr.var $(quote x.getId.toString) rfl : Expr _ _))
  | `(`[Expr|$x = $y])  => `(Expr.binop `[Expr|$x] BinOp.eq `[Expr|$y])
  | `(`[Expr|$x && $y]) => `(Expr.binop `[Expr|$x] BinOp.and `[Expr|$y])
  | `(`[Expr|$x < $y])  => `(Expr.binop `[Expr|$x] BinOp.lt `[Expr|$y])
  | `(`[Expr|$x + $y])  => `(Expr.binop `[Expr|$x] BinOp.add `[Expr|$y])
  | `(`[Expr|$x - $y])  => `(Expr.binop `[Expr|$x] BinOp.sub `[Expr|$y])
  | `(`[Expr|($x)])     => `(`[Expr|$x])

declare_syntax_cat com


syntax ident " := " term ";\n" : com
syntax "if " "(" term ")" " {\n" com* "\n}" (" else " "{\n" com* "\n}")? : com
syntax "while " "(" term ")" " {\n" com* "\n}" : com

syntax "`[Com|" com* "]" : term

macro_rules
  | `(`[Com|])                    => `(Com.skip)
  | `(`[Com|$x:ident := $e;])     => `(Com.ass $(quote x.getId.toString) `[Expr|$e] rfl)
  | `(`[Com|if ($b) { $cts* } else { $cfs* }]) =>
    `(Com.cond `[Expr|$b] `[Com|$cts*] `[Com|$cfs*])
  | `(`[Com|if ($b) { $cts* }])   => `(`[Com|if ($b) { $cts* } else {}])
  | `(`[Com|while ($b) { $cs* }]) => `(Com.while `[Expr|$b] `[Com|$cs*])
  | `(`[Com|$c $cs*])             => `(Com.seq `[Com|$c] `[Com|$cs*])

end While

namespace test

open While
open Expr
open Map

abbrev Γ : Ctxt := Map.empty["x" ↦ Ty.int]["y" ↦ Ty.int]["b" ↦ Ty.bool]

def e01 :  Expr Γ Ty.bool := `[Expr| true]
def e02 :  Expr Γ Ty.bool := `[Expr| false]
def e03 :  Expr Γ Ty.int  := `[Expr| 42]
def e04a : Expr Γ Ty.int  := `[Expr| x]
def e04b : Expr Γ Ty.bool := `[Expr| b]
def e06 :  Expr Γ Ty.bool := `[Expr| 42 = 28]
def e07 :  Expr Γ Ty.bool := `[Expr| true && false]
def e08 :  Expr Γ Ty.bool := `[Expr| 0 < 1]
def e09 :  Expr Γ Ty.int  := `[Expr| 1 + 1]
def e10 :  Expr Γ Ty.int  := `[Expr| 42 - 28]
def e11 :  Expr Γ Ty.bool := `[Expr| (10 + 4 < 15 - 1) && (42 = 28 + x) && b]

def example1 : Com Γ := `[Com|
  x := 8;
  y := 10;
  if (x < y) {
    x := x + 1;
  } else {
    y := y + 3;
  }]
#reduce example1

def example2 : Com Γ := `[Com|
  x := 8;
  if (x < y) {
    x := x + 1;
  } else {
    y := y + 3;
    x := 9;
  }
  y := x;]
#reduce example2

def example3 : Com Γ := `[Com|
  if (x < 10) {
    x := 8;
  } else {
    x := 14;
  }
  while (x < 7) {
    x :=  x + x;
  }]
#reduce example3

def example4 : Com Γ := `[Com|
  x := 13;
  y := 7;
  while (y = x - 5) {
    x := x + 1;
  }]
#reduce example4

end test
