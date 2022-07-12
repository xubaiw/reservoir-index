import TBA.While.Solution

namespace testing

open While
open Optimisation
open Expr
open Map
open State

abbrev Γ : Ctxt := Map.empty["x" ↦ Ty.int]["y" ↦ Ty.int]["z" ↦ Ty.int]["b" ↦ Ty.bool]

#reduce foldExpr State.empty `[Expr| 5 + 4 - 9 = 0]
#reduce foldExpr State.empty `[Expr| 1 - 4 < (5 + 5) - (10 + 3)]
#reduce foldExpr State.empty `[Expr| 1 + 2]

def com1 : Com Γ := `[Com|
  x := 7;
  y := 3;
  if (x = y) {
    y := x + 2;
  } else {
    y := x - z;
    z := y;
  }]
#reduce optimise com1

def com2 : Com Γ := `[Com|
  x := 2;
  y := x;
  b := x = y;
  if (b) {
    z := x + y;
  } else {
    z := x;
  }]
#reduce optimise com2

def com3 : Com Γ := `[Com|
  x := 13;
  y := 7;
  while (y = x - 5) {
    x := x + 1;
  }]
#reduce optimise com3

def com4 : Com Γ := `[Com|
  x := 8;
  if (x < y) {
    x := x + 1;
  } else {
    y := y + 3;
    x := 9;
  }
  y := x;]
#reduce optimise com4

def com5 : Com Γ := `[Com|
  if (x < y) {
    x := 9;
    y := x + 1;
  } else {
    x := 9;
    y := x - 1;
  }
  z := x + y;]
#reduce optimise com5

end testing
