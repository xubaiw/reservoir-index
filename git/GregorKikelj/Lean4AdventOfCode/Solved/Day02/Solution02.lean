
def parse(cmd:String)(n:Int):(Int × Int) :=
  if cmd=="forward" then
    (n, 0)
  else if cmd=="down" then
    (0, n)
  else
    (0, -n)

def parseCommands(comds:List String)(pos:Int × Int) : (Int × Int) :=
  match comds with
  | [] => pos
  | h::t => 
    match String.splitOn h with
    | [cmd, num] => let (x, y) := parse cmd (String.toInt! num)
                    parseCommands t (pos.fst+x, pos.snd+y)
    | _ => panic "Split failure"


def solvePart21 (s : String) : IO String := do
    let input ← IO.FS.lines s
    let pos := parseCommands input.toList (0,0)
    return s!"{pos.fst*pos.snd}"


-- pair of aim and pos
def parse2(cmd:String)(n:Int)(aim:Int)(pos: Int × Int):Int × (Int × Int):=
  if cmd=="forward" then
    (aim, (pos.fst+n, pos.snd+n*aim)) 
  else if cmd=="down" then
    (aim+n, pos)
  else
    (aim-n, pos)


def parseCommands2(cmds:List String)(aim:Int)(pos: Int × Int): (Int × Int) :=
  match cmds with
  |[] => pos
  |h::t => 
    match String.splitOn h with
    | [cmd, num] => let (aim2, pos2):= parse2 cmd (String.toInt! num) aim pos
                    parseCommands2 t aim2 pos2
    | _ => panic "Split2 failure"

def solvePart22 (s : String) : IO String := do
    let input ← IO.FS.lines s
    let pos := parseCommands2 input.toList 0 (0,0)
    return s!"{pos.fst*pos.snd}"



