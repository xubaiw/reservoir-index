
def ls_to_li (ls:List String) : List Int :=
    match ls with
    | [] => []
    | (h::t) => (String.toInt! h:: ls_to_li t)


def printListSum(li: List Int) : IO Int := do
    let mut sum := 0
    for l in li do
        IO.println l
        sum := sum + l
    return sum

def arr_str_to_arr_int(arr_s : Array String) : Array Int :=
    arr_s.map String.toInt!

def score(arr: Array Int) : Int := Id.run <| do
    let mut score :=0
    for i in [1:arr.size ] do
        if arr[i-1]<arr[i] then
            score := score+1
    return score

def solvePart11 (s : String) : IO String := do
    let input ← IO.FS.lines s
    let int_lines := arr_str_to_arr_int input
    let score := score int_lines
    return s!"{score}"

def score2(arr: Array Int) : Int := Id.run <| do
    let mut score :=0
    for i in [3:arr.size ] do
        if arr[i-3]<arr[i] then
            score := score+1
    return score

def solvePart12 (s : String) : IO String := do
    let input ← IO.FS.lines s
    let int_lines := arr_str_to_arr_int input
    let score := score2 int_lines
    return s!"{score}"

#eval solvePart11 "Solved/Day01/small.txt"
#eval solvePart12 "Solved/Day01/small.txt"
