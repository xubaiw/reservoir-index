import TBA.While.Solution

namespace While

namespace Optimisation

#reduce foldExpr Map.empty `[Expr| 5 + 4 - 9 = 0]
#reduce foldExpr Map.empty `[Expr| 1 - 4 < (5 + 5) - (10 + 3)]
#reduce foldExpr Map.empty `[Expr| 1 + true]

def com1 := `[Com| 
  x := 7;
  y := 3;
  if (x = y) {
    y := x + 2;
  } else {
    y := x - z;
    z := y;
  }]
#reduce optimise com1

def com2 := `[Com| 
  x := 2;
  y := x;
  b := x = y;
  if (b) {
    z := x + y;
  } else {
    z := x;
  }]
#reduce optimise com2

def com3 := `[Com|
  x := 13;
  y := 7;
  while (y = x - 5) {
    x := x + 1;
  }]
#reduce optimise com3

def com4 := `[Com|
  x := 8;
  if (x < y) {
    x := x + 1;
  } else {
    y := y + 3;
    x := 9;
  }
  y := x;]
#reduce optimise com4

def com5 := `[Com|
  if (x < y) {
    x := 9;
    y := x + 1;
  } else {
    x := 9;
    y := x - 1;
  }
  z := x + y;]
#reduce optimise com5

end Optimisation

end While