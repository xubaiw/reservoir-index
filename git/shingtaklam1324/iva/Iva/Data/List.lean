variable {α : Type u}

namespace List

def pairs : List α → List (α × α)
| [] => []
| x :: xs => xs.map (x, ·) ++ pairs xs

end List
