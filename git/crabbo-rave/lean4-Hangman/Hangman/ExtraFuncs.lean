open System
open IO
open Lean

namespace ExtraFuncs

partial def List.unfoldr (f : β → Option (α × β)) (s : β) : List α := 
  match f s with
  | none => []
  | some (a, b') => a::(unfoldr f b')

def getRandomSentence (sentences : Array String) (i : Nat) : String := 
  sentences[(i % sentences.toList.length) - 1]

def sentenceFileTxt : String := include_str% "sentences.txt"

def getRandomSentence' (filename : FilePath) : Array String := do
  let fconts : String ← FS.readFile filename
  pure $ fconts.split (·='\n').toArray
   
end ExtraFuncs

open ExtraFuncs

-- def List.unfoldr' {α β : Type u} [sz : SizeOf β] (f : (b : β) → Option (α × { b' : β // sizeOf b' < sizeOf b})) (b : β) : List α :=
--   match f b with
--   | none => []
--   | some (a, ⟨b', h⟩) => a :: unfoldr' f b'

-- def List.unfoldr {α β : Type u} [sz : SizeOf β] (f : (b : β) → Option (α × { b' : β // sizeOf b' < sizeOf b})) (b : β) : List α :=
--   match f b with
--   | none => []
--   | some (a, ⟨b', h⟩) => a :: unfoldr f b'

def foo := "helloworld".toList.toArray.map (toString ·)


#eval foo
#eval getRandomSentence foo 15787
#print getRandomSentence'