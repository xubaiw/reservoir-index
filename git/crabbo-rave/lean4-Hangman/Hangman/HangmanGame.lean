import Hangman.ExtraFuncs
open ExtraFuncs

structure HangmanGame where
  zippedWord : List (Char × Char)
  lettersGuessed : List String
  tryCount : Nat

instance : ToString HangmanGame where
  toString state := 
    s!"Zipped word: {state.zippedWord}¬Guessed letters {state.lettersGuessed}"

namespace HangmanGame

def convertToHiddenChar : Char → Char 
  | ' ' => ' '
  | _ => '_'

def convertToHiddenWord (str : String) : List (Char × Char) :=
  str
  |>.toList 
  |>.map (λ c => (c, convertToHiddenChar c))

def joinHiddenWord (state : HangmanGame) : String :=
  state.zippedWord
  |>.foldr (λ t accstr => (toString t.snd) ++ accstr) ""

def joinWord (state : HangmanGame) : String :=
  state.zippedWord
  |>.foldr (λ t accstr => (toString t.fst) ++ accstr) ""

def revealLetter (state : HangmanGame) (c : Char) : HangmanGame :=
  let newZippedWords := 
    state.zippedWord
    |>.map (λ t => if t.fst = c then (t.fst, c) else (t.fst, t.snd))
  { state with zippedWord := newZippedWords }

def isEqualToWord (state : HangmanGame) (word : String) :=
  word = joinWord state

end HangmanGame

namespace HangmanGame

def init (word : String) : HangmanGame :=
  let zippedWord := convertToHiddenWord word 
  { zippedWord := zippedWord, lettersGuessed := [], tryCount := 0 }

def runGame (state : HangmanGame) (iarg : Nat) : IO UInt32 := do 
  let _ := List.unfoldr (λ (st : HangmanGame) => 
                        if st.tryCount < 15 then
                          )
  pure 0

end HangmanGame

def abj := HangmanGame.init "apple bottom jeans"

#eval abj.joinHiddenWord

#eval abj 
  |>.revealLetter 'a' 
  |>.revealLetter 'e' 
  |>.revealLetter 'o' 
  |>.revealLetter 's' 
  |>.revealLetter 'p' 
  |>.revealLetter 'l' 
  |>.revealLetter 't' 
  |>.joinHiddenWord