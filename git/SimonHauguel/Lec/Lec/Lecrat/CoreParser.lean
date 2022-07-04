import Std.Data.HashMap

open Lean Std HashMap

universe u

-- Lecrat is a DSL that claims to describe a pep-like and generates a packrat parser

-- RatValue is the AST that is generated by the lecrat parser 
inductive RatValue (α : Type u) where
  -- a | b
  | OR         : RatValue α   × RatValue α                 → RatValue α
  -- a b 
  | COMP       : RatValue α   × RatValue α                 → RatValue α 
  -- a where a is not terminal
  | REF        : Lean.Name                                 → RatValue α
  -- a where a is terminal
  | STRING     : String                                    → RatValue α
  -- a*
  | MANY       : RatValue α                                → RatValue α
  -- a+
  | SOME       : RatValue α                                → RatValue α
  -- a?
  | OPTION     : RatValue α                                → RatValue α
  -- bind ← a
  | NAMED      : Lean.Name    → RatValue α                 → RatValue α
  -- a => fun
  | COMPTO     : RatValue α   → (HashMap Lean.Name α → α)  → RatValue α
  -- ε do nothing
  | NIL        : RatValue α
  deriving Inhabited

open RatValue

notation:10 lrv " ∣ "  rrv:10    => OR ⟨lrv, rrv⟩
notation:54 lrv " ⊹ " rrv:55    => COMP ⟨lrv, rrv⟩
notation        "*"   rrv:80    => MANY rrv
notation        "+"   rrv:80    => SOME rrv
notation        "?"   rrv:70    => OPTION rrv
notation        "$"   name:90   => STRING name
notation        "↑"   name:90   => REF name
notation:45 lrv "←"   rrv:45    => NAMED lrv rrv     
notation        "ε"             => NIL
notation:30 lrv "{>" val "<}"   => COMPTO lrv val

macro n:term "IsAGrammarThatProducesA" typ:term "Where" terms:many(term) "EndGrammar" :command => 
  `(def $n : HashMap Lean.Name (RatValue $typ) :=
      HashMap.ofList [$terms,*])

macro n:term "IsAGrammarThatProducesA" typ:term "With" depends:term
      "Where" terms:many(term) "EndGrammar" :command =>
    `(def $n : HashMap Lean.Name (RatValue $typ) :=
      HashMap.ofList (
        List.foldr ((.++.) ∘ HashMap.toList) [$terms,*] $depends
      ))

macro X:term "::=" V:term ";;" :term => `(⟨$X, $V⟩)

-- Note : pos makes no sens, but you know
structure Parser (α : Type u) (β : Type u) where
  mkParser ::
    entry       : String
    pos         : Int × Int                      := ⟨0, 0⟩ 
    context     : HashMap Lean.Name α            := empty
    extensions  : HashMap Lean.Name (RatValue α) := empty
    error       : Option β                       := none
    result      : α

open Parser

-- To be a valid AST, you need to satisfy 3 things :
-- 1 . You need to give a way to capture *meta terminal symbol*
-- 2 . You need to give a way to concatenate the result of a many/some
-- 3 . You need to give a way to parse *nothing*
-- Note : (α, resultMultiParser, resultMetaNil) is a Monoid
class CanProduceParsingResult (α : Type u) where
  resultMetaString  : String → α
  resultMultiParser : α → α → α 
  resultMetaNil     : α

-- This class is quite useless actually, exists only to build polymorphic parser on error type
class CanProduceErrorFromContext (β : Type u) where
  fromParserContext : Parser α β → β  



-- Everything below is "useless", hardcoded and is intended to be deleted soon 

def String.mkParserFromString (entry : String) (α : Type _) [Inhabited α] (β : Type _) : Parser α β :=
  mkParser entry ⟨0, 0⟩ default default default default

instance [Inhabited α] : Inhabited (Parser α β) where
  default := "".mkParserFromString α β

instance : CanProduceParsingResult String where
  resultMetaString  := id
  resultMetaNil     := ""
  resultMultiParser := (.++.)

def stringToNat (s : String) : Int :=
  match s with
  | "0" => 0
  | "1" => 1
  | "2" => 2
  | "3" => 3
  | "4" => 4
  | "5" => 5
  | "6" => 6
  | "7" => 7
  | "8" => 8
  | "9" => 9
  | _ => panic! "ERROR String to Nat"
  
instance : CanProduceParsingResult Int where
  resultMetaString := stringToNat
  resultMetaNil := 0
  resultMultiParser := (.+.)

abbrev Error := Bool

instance : CanProduceErrorFromContext Error where
  fromParserContext _ := true