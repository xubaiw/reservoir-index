import Std.Data.RBTree

section Utils
  /--
  Matches the lengths of lists `a` and `b` by filling the shorter one with
  `unit` elements at the tail end. The matched lists are returned in the same order
  as they were passed.
  -/
  def List.matchLength (a : List α) (b : List α) (unit : α) : List α × List α :=
    if a.length < b.length then
      (a ++ .replicate (b.length - a.length) unit, b)
    else
      (a, b ++ .replicate (a.length - b.length) unit)

  namespace Array
    -- not really used anymore, but still a neat function to have!
    /--
    Groups elements in `xs` by `key` such that the returned array contains arrays of elements
    from `xs` that are all equal after being mapped with `key`.
    -/
    def groupBy [Inhabited α] [Inhabited β] [LT α] [DecidableRel ((· < ·) : α → α → Prop)]
      (key : β → α) (xs : Array β)
      : Array (Array β) := Id.run do
      if xs.size = 0 then
        return #[]
      let xs := xs.qsort (key · < key ·)
      let mut groups : Array (Array β) := #[#[]]
      let mut currentRepresentative := key xs[0]
      for x in xs do
        let k := key x
        if k < currentRepresentative ∨ k > currentRepresentative then
          groups := groups.push #[x]
          currentRepresentative := k
        else
          let lastIdx := groups.size - 1
          groups := groups.set! lastIdx <| groups[lastIdx].push x
      return groups

    def join (xss : Array (Array α)) : Array α := Id.run do
      let mut r := #[]
      for xs in xss do
        r := r ++ xs
      return r

    def flatMap (f : α → Array β) (xs : Array α) : Array β :=
      xs.map f |>.join
  end Array

  namespace String
    /--
    Inserts newlines `\n` into `s` after every `maxWidth` characters so that the result
    contains no line longer than `maxWidth` characters. Retains newlines `\n` in `s`.
    Yields `none` if `maxWidth = 0`.
    -/
    def wrapAt? (s : String) (maxWidth : Nat) : Option String := Id.run do
      if maxWidth = 0 then
        return none
      let lines := s.splitOn "\n" |>.map fun line => Id.run do
        let resultLineCount :=
          if line.length % maxWidth = 0 then
            line.length / maxWidth
          else
            line.length / maxWidth + 1
        let mut line := line
        let mut result := #[]
        for i in [:resultLineCount] do
          result := result.push <| line.take maxWidth
          line := line.drop maxWidth
        return "\n".intercalate result.toList
      return "\n".intercalate lines

    /--
    Inserts newlines `\n` into `s` after every `maxWidth` characters so that the result
    contains no line longer than `maxWidth` characters. Retains newlines `\n` in `s`.
    Panics if `maxWidth = 0`.
    -/
    def wrapAt! (s : String) (maxWidth : Nat) : String :=
      s.wrapAt? maxWidth |>.get!

    /--
    Deletes all trailing spaces at the end of every line, as seperated by `\n`.
    -/
    def trimTrailingSpaces (s : String) : String :=
      s.splitOn "\n" |>.map (·.dropRightWhile (· = ' ')) |> "\n".intercalate

    /--
    Inserts newlines `\n` into `s` after every `maxWidth` characters before words
    that would otherwise be broken apart by the newline. The result will contain
    no line longer than `maxWidth` characters and no words except those already
    longer than `maxWidth` characters will be broken up in the middle.
    Removes trailing whitespace before each inserted newline. Retains newlines `\n` in `s`.
    Returns `none` if `maxWidth = 0`.
    -/
    def wrapWordsAt? (s : String) (maxWidth : Nat) : Option String := Id.run do
      if maxWidth = 0 then
        return none
      let wordWrappedLines : List String := s.splitOn "\n" |>.map fun s => Id.run do
        let words                : Array String := s.splitOn.toArray
        let mut currentLineWidth : Nat          := 0
        let mut result           : Array String := #[]
        for i in [:words.size] do
          let w := words[i]
          -- `w = ""`: we will never insert a newline on a space. this has the effect
          -- of inserting the newline only after a bunch of trailing whitespace, which we remove later.
          -- similarly, `currentLineWidth + w.length ≤ maxWidth` does not count the space after `w` so that
          -- we do not insert a newline before a word that fits except for a trailing space.
          if w = "" ∨ currentLineWidth + w.length ≤ maxWidth then
            -- `+ 1` because we count the space after `w` to accurately keep track of spaces.
            currentLineWidth := currentLineWidth + w.length + 1
            result := result.push w
            continue
          -- if `w` is the first proper word, this will insert a `\n` before the text, which we remove later.
          -- `w.wrapAt! maxWidth` ensures that our new line is not already too large.
          let wordOnNewLine := "\n" ++ w.wrapAt! maxWidth
          result := result.push wordOnNewLine
          let wrappedLines : Array String := wordOnNewLine.splitOn "\n" |>.toArray
          currentLineWidth := wrappedLines[wrappedLines.size - 1].length + 1
        return " ".intercalate result.toList
      let trimmed : List String :=
        wordWrappedLines.map trimTrailingSpaces
        |>.map fun line => Id.run do
          if line = "" then
            return ""
          if line[0] ≠ '\n' then
            return line
          return line.drop 1
      return "\n".intercalate trimmed

    /--
    Inserts newlines `\n` into `s` after every `maxWidth` characters before words
    that would otherwise be broken apart by the newline. The result will contain
    no line longer than `maxWidth` characters and no words except those already
    longer than `maxWidth` characters will be broken up in the middle.
    Removes trailing whitespace before each inserted newline. Retains newlines `\n` in `s`.
    Panics if `maxWidth = 0`.
    -/
    def wrapWordsAt! (s : String) (maxWidth : Nat) : String :=
      s.wrapWordsAt? maxWidth |>.get!

    /--
    Inserts `n` spaces before each line as seperated by `\n` in `s`.
    Does not indent `s = ""`.
    -/
    def indent (s : String) (n : Nat := 4) : String := Id.run do
      if s = "" then
        return ""
      return s.splitOn "\n" |>.map ("".pushn ' ' n ++ ·) |> "\n".intercalate

    /--
    Intercalates elements `≠ ""` in `xs` using `sep`.
    -/
    def optJoin (xs : Array String) (sep : String) : String :=
      xs.filter (· ≠ "") |>.toList |> sep.intercalate
  end String

  namespace Array
    /--
    Renders `rows` as a table with a maximum row width of `maxWidth` and a margin of `margin`
    between the columns. Wraps words according to `String.wrapWordsAt?` to ensure that no
    rendered row of the table is longer than `maxWidth`.
    Returns `none` if `(maxWidth-margin)/2` < 1, i.e. if there is not enough space for
    text in both columns.
    -/
    def renderTable? (rows : Array (String × String)) (maxWidth : Nat) (margin : Nat := 2)
      : Option String := Id.run do
      if rows.isEmpty then
        return ""
      let rightColumnWidth := rows.map (·.2.length) |>.getMax? (· < ·) |>.get!
      let minRightColumnWidth := Nat.min rightColumnWidth <| Nat.max ((maxWidth-margin)/2) 1
      if maxWidth - margin - minRightColumnWidth < 1 then
        return none
      let rows : Array (List String × String) := rows.map fun (left, right) =>
        (maxWidth - margin - minRightColumnWidth |> left.wrapWordsAt! |>.splitOn "\n", right)
      let leftColumnWidth :=
        rows.flatMap (·.1.map (·.length) |>.toArray)
          |>.getMax? (· < ·)
          |>.get!
      let leftColumnWidth := leftColumnWidth + margin
      let rows : Array (List String × List String) := rows.map fun (left, right) =>
        (left, maxWidth - leftColumnWidth |> right.wrapWordsAt! |>.splitOn "\n")
      let rows : Array (String × String) := rows.flatMap fun (left, right) =>
        let (left, right) : List String × List String := left.matchLength right ""
        left.zip right |>.toArray
      let rows : Array String := rows.map fun (left, right) =>
        if right = "" then
          left
        else
          let padding := "".pushn ' ' (leftColumnWidth - left.length)
          left ++ padding ++ right
      return "\n".intercalate rows.toList

    /--
    Renders `rows` as a table with a maximum row width of `maxWidth` and a margin of `margin`
    between the columns. Wraps words according to `String.wrapWordsAt?` to ensure that no
    rendered row of the table is longer than `maxWidth`.
    Panics if `(maxWidth-margin)/2` < 1, i.e. if there is not enough space for
    text in both columns.
    -/
    def renderTable! (rows : Array (String × String)) (maxWidth : Nat) (margin : Nat := 2)
      : String :=
      rows.renderTable? maxWidth margin |>.get!
  end Array

  namespace Option
    def join (x : Option (Option α)) : Option α := OptionM.run do ←x

    /--
    Returns `""` if the passed `Option` is `none`, otherwise
    converts the contained value using a `ToString` instance.
    -/
    def optStr [ToString α] : Option α → String
    | none   => ""
    | some v => toString v
  end Option
end Utils

namespace Cli

section Configuration
  /--
  Represents a type that can be parsed to a string and the corresponding name of the type.
  Used for converting parsed user input to the respective expected type.
  -/
  class ParseableType (τ) where
    /-- Name of the type, used when displaying the help. -/
    name   : String
    /-- Function to parse a value to the type that returns `none` if it cannot be parsed. -/
    parse? : String → Option τ

  instance : ParseableType Unit where
    name     := "Unit"
    parse? s := ()

  instance : ParseableType Bool where
    name := "Bool"
    parse?
    | "true"  => true
    | "false" => false
    | _       => none

  instance : ParseableType String where
    name     := "String"
    parse? s := s

  instance : ParseableType Nat where
    name := "Nat"
    parse?
      -- HACK: temporary workaround for minor bug in String.toNat?
      | "" => none
      | s  => s.toNat?

  instance : ParseableType Int where
    name := "Int"
    parse?
      -- HACK: temporary workaround for minor bug in String.toInt?
      | "" => none
      | s  => s.toInt?

  instance [inst : ParseableType α] : ParseableType (Array α) where
    name :=
      if inst.name.contains ' ' then
        s!"Array ({inst.name})"
      else
        s!"Array {inst.name}"
    parse?
    | "" => some #[]
    | s  => OptionM.run do return (← s.splitOn "," |>.mapM inst.parse?).toArray

  /--
  Represents the type of some flag or argument parameter. Typically coerced from types with
  `ParseableType` instances such that `isValid := (ParseableType.parse? · |>.isSome)`.
  -/
  structure ParamType where
    /-- Name of the type, used when displaying the help. -/
    name    : String
    /-- Function to check whether a value conforms to the type. -/
    isValid : String → Bool
    deriving Inhabited

  instance : BEq ParamType where
    beq a b := a.name == b.name

  instance : Repr ParamType where
    reprPrec p n := p.name

  instance [inst : ParseableType τ] : CoeDep Type τ ParamType where
    coe := ⟨inst.name τ, (inst.parse? · |>.isSome)⟩

  /--
  Represents a flag, usually known as "option" in standard terminology.
  -/
  structure Flag where
    /-- Designates `x` in `-x`. -/
    shortName?  : Option String := none
    /-- Designates `x` in `--x`. -/
    longName    : String
    /-- Description that is displayed in the help. -/
    description : String
    /--
    Type according to which the parameter is validated.
    `Unit` is used to designate flags without a parameter.
    -/
    type        : ParamType
    deriving Inhabited, BEq, Repr

  namespace Flag
    /--
    Initializes a flag without a parameter. Parameterless flags are
    designated by the `Unit` type.
    - `shortName?`:  Designates `x` in `-x`.
    - `longName`:    Designates `x` in `--x`.
    - `description`: Description that is displayed in the help.
    -/
    def paramless
      (shortName?  : Option String := none)
      (longName    : String)
      (description : String)
      : Flag := {
        shortName?  := shortName?
        longName    := longName
        description := description
        type        := Unit
      }

    /-- Designates `x` in `-x`. -/
    def shortName!   (f : Flag) : String := f.shortName?.get!
    /-- Checks whether `f` has an associated short flag name `x` in `-x`. -/
    def hasShortName (f : Flag) : Bool   := f.shortName?.isSome

    /-- Checks whether `f` has a `Unit` type. -/
    def isParamless  (f : Flag) : Bool := f.type == Unit
  end Flag

  /--
  Represents an argument (either positional or variable),
  usually known as "operand" in standard terminology
  -/
  structure Arg where
    /- Name that is displayed in the help. -/
    name        : String
    /- Description that is displayed in the help. -/
    description : String
    /- Description that is displayed in the help. -/
    type        : ParamType
    deriving Inhabited, BEq, Repr

  namespace Parsed
    /--
    Represents a flag and its parsed value.
    Use `Parsed.Flag.as!` to convert the value to some `ParseableType`.
    -/
    structure Flag where
      /-- Associated flag meta-data. -/
      flag  : Flag
      /-- Parsed value that was validated and conforms to `flag.type`. -/
      value : String
      deriving Inhabited, BEq, Repr

    instance : ToString Flag where
      toString f := s!"--{f.flag.longName}" ++ (if f.value ≠ "" then s!"={f.value}" else "")

    namespace Flag
      /--
      Converts `f.value` to `τ`, which should be the same type
      that was designated in `f.flag.type`.
      Yields `none` if the conversion was unsuccessful, which can only
      happen if `τ` is not the same type as the one designated in `f.flag.type`.
      -/
      def as? (f : Flag) (τ) [ParseableType τ] : Option τ :=
        ParseableType.parse? f.value
      /--
      Converts `f.value` to `τ`, which should be the same type
      that was designated in `f.flag.type`.
      Panics if the conversion was unsuccessful, which can only
      happen if `τ` is not the same type as the one designated in `f.flag.type`.
      -/
      def as! (f : Flag) (τ) [Inhabited τ] [ParseableType τ] : τ :=
        f.as? τ |>.get!
    end Flag

    /--
    Represents an argument and its parsed value.
    Use `Parsed.Arg.as!` to convert the value to some `ParseableType`.
    -/
    structure Arg where
      /-- Associated argument meta-data. -/
      arg   : Arg
      /-- Parsed value that was validated and conforms to `arg.type`. -/
      value : String
      deriving Inhabited, BEq, Repr

    instance : ToString Arg where
      toString a := s!"<{a.arg.name}={a.value}>"

    namespace Arg
      /--
      Converts `a.value` to `τ`, which should be the same type
      that was designated in `a.arg.type`.
      Yields `none` if the conversion was unsuccessful, which can only
      happen if `τ` is not the same type as the one designated in `a.arg.type`.
      -/
      def as? (a : Arg) (τ) [ParseableType τ] : Option τ :=
        ParseableType.parse? a.value
      /--
      Converts `a.value` to `τ`, which should be the same type
      that was designated in `a.arg.type`.
      Panics if the conversion was unsuccessful, which can only
      happen if `τ` is not the same type as the one designated in `a.arg.type`.
      -/
      def as! (a : Arg) (τ) [Inhabited τ] [ParseableType τ] : τ :=
        a.as? τ |>.get!
    end Arg
  end Parsed

  /-- Represents all the non-recursive meta-data of a command. -/
  structure Cmd.Meta where
    /-- Name that is displayed in the help. -/
    name                : String
    /--
    Names of the commands of which this command is a subcommand.
    Corresponds to the path from the root to this command. Typically
    initialized by `Cmd.mk` or `Cmd.mk'`.
    -/
    parentNames         : Array String
    /-- Version of the command that is displayed in the help and when the version is queried. -/
    version             : String
    /-- Description that is displayed in the help. -/
    description         : String
    /-- Information appended to the end of the help. Useful for command extensions. -/
    furtherInformation? : Option String := none
    /-- Supported flags ("options" in standard terminology). -/
    flags               : Array Flag
    /-- Supported positional arguments ("operands" in standard terminology). -/
    positionalArgs      : Array Arg
    /-- Variable argument after the end of the positional arguments. -/
    variableArg?        : Option Arg
    deriving Inhabited, BEq, Repr

  namespace Cmd.Meta
    /-- Full name from the root to this command, including the name of the command itself. -/
    def fullName (m : Meta) : String := m.parentNames.push m.name |>.toList |> " ".intercalate

    /-- Information appended to the end of the help. Useful for command extensions. -/
    def furtherInformation! (m : Meta) : String := m.furtherInformation?.get!
    /-- Variable argument after the end of the positional arguments. -/
    def variableArg!        (m : Meta) : Arg    := m.variableArg?.get!

    /-- Checks whether `m` has information appended to the end of the help. -/
    def hasFurtherInformation (m : Meta) : Bool := m.furtherInformation?.isSome
    /-- Checks whether `m` supports a variable argument. -/
    def hasVariableArg        (m : Meta) : Bool := m.variableArg?.isSome

    /-- Finds the flag in `m` with the corresponding `longName`. -/
    def flag?          (m : Meta) (longName : String) : Option Flag   := m.flags.find? (·.longName = longName)
    /-- Finds the positional argument in `m` with the corresponding `name`. -/
    def positionalArg? (m : Meta) (name     : String) : Option Arg    := m.positionalArgs.find? (·.name = name)

    /-- Finds the flag in `m` with the corresponding `longName`. -/
    def flag!          (m : Meta) (longName : String) : Flag   := m.flag? longName |>.get!
    /-- Finds the positional argument in `m` with the corresponding `name`. -/
    def positionalArg! (m : Meta) (name     : String) : Arg    := m.positionalArg? name |>.get!

    /-- Checks whether `m` contains a flag with the corresponding `longName`. -/
    def hasFlag          (m : Meta) (longName : String) : Bool := m.flag? longName |>.isSome
    /-- Checks whether `m` contains a positional argument with the corresponding `name`. -/
    def hasPositionalArg (m : Meta) (name     : String) : Bool := m.positionalArg? name |>.isSome

    /-- Finds the flag in `m` with the corresponding `shortName`. -/
    def flagByShortName? (m : Meta) (name : String) : Option Flag :=
      m.flags.findSome? fun flag => OptionM.run do
        let shortName ← flag.shortName?
        guard <| shortName = name
        return flag

    /-- Finds the flag in `m` with the corresponding `shortName`. -/
    def flagByShortName! (m : Meta) (name : String) : Flag := m.flagByShortName? name |>.get!

    /-- Checks whether `m` has a flag with the corresponding `shortName`. -/
    def hasFlagByShortName (m : Meta) (name : String) : Bool := m.flagByShortName? name |>.isSome
  end Cmd.Meta

  structure Parsed where
    /-- Non-recursive meta-data of the associated command. -/
    cmd            : Cmd.Meta
    /-- Parsed flags. -/
    flags          : Array Parsed.Flag
    /-- Parsed positional arguments. -/
    positionalArgs : Array Parsed.Arg
    /-- Parsed variable arguments. -/
    variableArgs   : Array Parsed.Arg
    deriving Inhabited, BEq, Repr

  namespace Parsed
    /-- Finds the parsed flag in `p` with the corresponding `longName`. -/
    def flag?          (p : Parsed) (longName : String) : Option Flag := p.flags.find? (·.flag.longName = longName)
    /-- Finds the parsed positional argument in `p` with the corresponding `name`. -/
    def positionalArg? (p : Parsed) (name : String)     : Option Arg  := p.positionalArgs.find? (·.arg.name = name)

    /-- Finds the parsed flag in `p` with the corresponding `longName`. -/
    def flag!          (p : Parsed) (longName : String) : Flag := p.flag? longName |>.get!
    /-- Finds the parsed positional argument in `p` with the corresponding `name`. -/
    def positionalArg! (p : Parsed) (name : String)     : Arg  := p.positionalArg? name |>.get!

    /-- Checks whether `p` has a parsed flag with the corresponding `longName`. -/
    def hasFlag          (p : Parsed) (longName : String) : Bool := p.flag? longName |>.isSome
    /-- Checks whether `p` has a positional argument with the corresponding `longName`. -/
    def hasPositionalArg (p : Parsed) (name : String)     : Bool := p.positionalArg? name |>.isSome

    /--
    Converts all `p.variableArgs` values to `τ`, which should be the same type
    that was designated in the corresponding `Cli.Arg`.
    Yields `none` if the conversion was unsuccessful, which can only
    happen if `τ` is not the same type as the one designated in the corresponding `Cli.Arg`.
    -/
    def variableArgsAs? (p : Parsed) (τ) [ParseableType τ] : Option (Array τ) :=
      OptionM.run <| p.variableArgs.mapM (·.as? τ)

    /--
    Converts all `p.variableArgs` values to `τ`, which should be the same type
    that was designated in the corresponding `Cli.Arg`.
    Panics if the conversion was unsuccessful, which can only
    happen if `τ` is not the same type as the one designated in the corresponding `Cli.Arg`.
    -/
    def variableArgsAs! (p : Parsed) (τ) [Inhabited τ] [ParseableType τ] : Array τ :=
      p.variableArgsAs? τ |>.get!

    instance : ToString Parsed where
      toString p :=
        s!"cmd: {p.cmd.fullName}; flags: {toString p.flags}; positionalArgs: {toString p.positionalArgs}; " ++
        s!"variableArgs: {toString p.variableArgs}"
  end Parsed

  /--
  Allows user code to extend the library in two ways:
  - The `meta` of a command can be replaced or extended with new components to adjust the displayed help.
  - The output of the parser can be postprocessed and validated.
  -/
  structure Extension where
    /-- Extends the `meta` of a command to adjust the displayed help. -/
    extendMeta  : Cmd.Meta → Cmd.Meta := id
    /-- Processes and validates the output of the parser with the extended `meta` as extra information. -/
    postprocess : Cmd.Meta → Parsed → Except String Parsed := fun m => pure
    deriving Inhabited

  /--
  Composes both extensions so that the `meta`s are extended in succession
  and postprocessed in succession. Postprocessing errors if any of the two
  `postprocess` functions errors and feeds the `meta` extended with `a.extendMeta`
  into `b.postprocess`.
  -/
  def Extension.then (a : Extension) (b : Extension) : Extension := {
    extendMeta  := b.extendMeta ∘ a.extendMeta
    postprocess := fun meta parsed => do
      let meta' := a.extendMeta meta
      b.postprocess meta' <| ← a.postprocess meta parsed
  }

  open Cmd in
  /--
  Represents a command, i.e. either the application root or some subcommand of the root.
  -/
  inductive Cmd
    | init
      (meta       : Meta)
      (run        : Parsed → IO UInt32)
      (subCmds    : Array Cmd)
      (extension? : Option Extension)

  open Inhabited in
  instance : Inhabited Cmd where
    default := Cmd.init default default default default

  namespace Cmd
    /-- Non-recursive meta-data. -/
    def meta       : Cmd → Cmd.Meta             | init v _ _ _ => v
    /-- Handler to run when the command is called and flags/arguments have been successfully processed. -/
    def run        : Cmd → (Parsed → IO UInt32) | init _ v _ _ => v
    /-- Subcommands. -/
    def subCmds    : Cmd → Array Cmd            | init _ _ v _ => v
    /-- Extension of the Cli library. -/
    def extension? : Cmd → Option Extension     | init _ _ _ v => v

    /-- Name that is displayed in the help. -/
    def name                (c : Cmd) : String        := c.meta.name
    /--
    Names of the commands of which `c` is a subcommand. Corresponds to the path from the root to `c`.
    Typically initialized by `Cmd.mk` or `Cmd.mk'`.
    -/
    def parentNames         (c : Cmd) : Array String  := c.meta.parentNames
    /-- Version of `c` that is displayed in the help and when the version is queried. -/
    def version             (c : Cmd) : String        := c.meta.version
    /-- Description that is displayed in the help. -/
    def description         (c : Cmd) : String        := c.meta.description
    /-- Information appended to the end of the help. Useful for command extensions. -/
    def furtherInformation? (c : Cmd) : Option String := c.meta.furtherInformation?
    /-- Supported flags ("options" in standard terminology). -/
    def flags               (c : Cmd) : Array Flag    := c.meta.flags
    /-- Supported positional arguments ("operands" in standard terminology). -/
    def positionalArgs      (c : Cmd) : Array Arg     := c.meta.positionalArgs
    /-- Variable argument at the end of the positional arguments. -/
    def variableArg?        (c : Cmd) : Option Arg    := c.meta.variableArg?

    /-- Full name from the root to `c`, including the name of `c` itself. -/
    def fullName (c : Cmd) : String := c.meta.fullName

    /-- Information appended to the end of the help. Useful for command extensions. -/
    def furtherInformation! (c : Cmd) : String    := c.meta.furtherInformation!
    /-- Variable argument after the end of the positional arguments. -/
    def variableArg!        (c : Cmd) : Arg       := c.meta.variableArg!
    /-- Extension of the Cli library. -/
    def extension!          (c : Cmd) : Extension := c.extension?.get!

    /-- Checks whether `c` has information appended to the end of the help. -/
    def hasFurtherInformation (c : Cmd) : Bool := c.meta.hasFurtherInformation
    /-- Checks whether `c` supports a variable argument. -/
    def hasVariableArg        (c : Cmd) : Bool := c.meta.hasVariableArg
    /-- Checks whether `c` is being extended. -/
    def hasExtension          (c : Cmd) : Bool := c.extension?.isSome

    /--
    Updates the designated fields in `c`.
    - `meta`:       Non-recursive meta-data.
    - `run`:        Handler to run when the command is called and flags/arguments have been successfully processed.
    - `subCmds`:    Subcommands.
    - `extension?`: Extension of the Cli library.
    -/
    def update'
      (c          : Cmd)
      (meta       : Meta               := c.meta)
      (run        : Parsed → IO UInt32 := c.run)
      (subCmds    : Array Cmd          := c.subCmds)
      (extension? : Option Extension   := c.extension?)
      : Cmd :=
      Cmd.init meta run subCmds extension?

    /--
    Updates the designated fields in `c`.
    - `name`:                Name that is displayed in the help.
    - `parentNames`:         Names of the commands of which `c` is a subcommand. Corresponds to the path from the root to `c`.
                             Typically initialized by `Cmd.mk` or `Cmd.mk'`.
    - `version`:             Version that is displayed in the help and when the version is queried.
    - `description`:         Description that is displayed in the help.
    - `furtherInformation?`: Information appended to the end of the help. Useful for command extensions.
    - `flags`:               Supported flags ("options" in standard terminology).
    - `positionalArgs`:      Supported positional arguments ("operands" in standard terminology).
    - `variableArg?`:        Variable argument at the end of the positional arguments.
    - `run`:                 Handler to run when the command is called and flags/arguments have been successfully processed.
    - `subCmds`:             Subcommands.
    - `extension?`:          Extension of the Cli library.
    -/
    def update
      (c                   : Cmd)
      (name                : String             := c.name)
      (parentNames         : Array String       := c.parentNames)
      (version             : String             := c.version)
      (description         : String             := c.description)
      (furtherInformation? : Option String      := c.furtherInformation?)
      (flags               : Array Flag         := c.flags)
      (positionalArgs      : Array Arg          := c.positionalArgs)
      (variableArg?        : Option Arg         := c.variableArg?)
      (run                 : Parsed → IO UInt32 := c.run)
      (subCmds             : Array Cmd          := c.subCmds)
      (extension?          : Option Extension   := c.extension?)
      : Cmd :=
      Cmd.init
        ⟨name, parentNames, version, description, furtherInformation?, flags, positionalArgs, variableArg?⟩
        run subCmds extension?

    /--
    Creates a new command. Adds a `-h, --help` and a `--version` flag.
    Updates the `parentNames` of all subcommands.
    - `meta`:       Non-recursive meta-data.
    - `run`:        Handler to run when the command is called and flags/arguments have been successfully processed.
    - `subCmds`:    Subcommands.
    - `extension?`: Extension of the Cli library.
    -/
    partial def mk'
      (meta       : Meta)
      (run        : Parsed → IO UInt32)
      (subCmds    : Array Cmd        := #[])
      (extension? : Option Extension := none)
      : Cmd := Id.run do
      let helpFlag := .paramless
        (shortName?  := "h")
        (longName    := "help")
        (description := "Prints this message.")
      let versionFlag := .paramless
        (longName    := "version")
        (description := "Prints the version.")
      let meta := { meta with flags := #[helpFlag, versionFlag] ++ meta.flags }
      let c := .init meta run subCmds extension?
      updateParentNames c
    where
      updateParentNames (c : Cmd) : Cmd :=
        let subCmds := c.subCmds.map fun subCmd =>
          let subCmd := updateParentNames subCmd
          subCmd.update (parentNames := #[meta.name] ++ subCmd.parentNames)
        c.update (subCmds := subCmds)

    /--
    Creates a new command. Adds a `-h, --help` and a `--version` flag.
    Updates the `parentNames` of all subcommands.
    - `name`:                Name that is displayed in the help.
    - `version`:             Version that is displayed in the help and when the version is queried.
    - `description`:         Description that is displayed in the help.
    - `furtherInformation?`: Information appended to the end of the help. Useful for command extensions.
    - `flags`:               Supported flags ("options" in standard terminology).
    - `positionalArgs`:      Supported positional arguments ("operands" in standard terminology).
    - `variableArg?`:        Variable argument at the end of the positional arguments.
    - `run`:                 Handler to run when the command is called and flags/arguments have been successfully processed.
    - `subCmds`:             Subcommands.
    - `extension?`:          Extension of the Cli library.
    -/
    def mk
      (name                : String)
      (version             : String)
      (description         : String)
      (furtherInformation? : Option String := none)
      (flags               : Array Flag    := #[])
      (positionalArgs      : Array Arg     := #[])
      (variableArg?        : Option Arg    := none)
      (run                 : Parsed → IO UInt32)
      (subCmds             : Array Cmd        := #[])
      (extension?          : Option Extension := none)
      : Cmd :=
      mk'
        ⟨name, #[], version, description, furtherInformation?, flags, positionalArgs, variableArg?⟩
        run subCmds extension?

    /-- Finds the flag in `c` with the corresponding `longName`. -/
    def flag?          (c : Cmd) (longName : String) : Option Flag := c.meta.flag? longName
    /-- Finds the positional argument in `c` with the corresponding `name`. -/
    def positionalArg? (c : Cmd) (name     : String) : Option Arg  := c.meta.positionalArg? name
    /-- Finds the subcommand in `c` with the corresponding `name`. -/
    def subCmd?        (c : Cmd) (name     : String) : Option Cmd  := c.subCmds.find? (·.name = name)

    /-- Finds the flag in `c` with the corresponding `longName`. -/
    def flag!          (c : Cmd) (longName : String) : Flag := c.meta.flag! longName
    /-- Finds the positional argument in `c` with the corresponding `name`. -/
    def positionalArg! (c : Cmd) (name     : String) : Arg  := c.meta.positionalArg! name
    /-- Finds the subcommand in `c` with the corresponding `name`. -/
    def subCmd!        (c : Cmd) (name     : String) : Cmd  := c.subCmd? name |>.get!

    /-- Checks whether `c` contains a flag with the corresponding `longName`. -/
    def hasFlag          (c : Cmd) (longName : String) : Bool := c.meta.hasFlag longName
    /-- Checks whether `c` contains a positional argument with the corresponding `name`. -/
    def hasPositionalArg (c : Cmd) (name     : String) : Bool := c.meta.hasPositionalArg name
    /-- Checks whether `c` contains a subcommand with the corresponding `name`. -/
    def hasSubCmd        (c : Cmd) (name     : String) : Bool := c.subCmd? name |>.isSome

    /-- Finds the flag in `c` with the corresponding `shortName`. -/
    def flagByShortName? (c : Cmd) (name : String) : Option Flag := c.meta.flagByShortName? name

    /-- Finds the flag in `c` with the corresponding `shortName`. -/
    def flagByShortName! (c : Cmd) (name : String) : Flag := c.meta.flagByShortName! name

    /-- Checks whether `c` has a flag with the corresponding `shortName`. -/
    def hasFlagByShortName (c : Cmd) (name : String) : Bool := c.meta.hasFlagByShortName name
  end Cmd
end Configuration

section Macro
  open Lean

  def expandIdentLiterally (s : Syntax) : Syntax :=
    if s.isIdent then
      quote s.getId.toString
    else
      s

  syntax positionalArg := colGe term " : " term "; " term

  def expandPositionalArg (positionalArg : Syntax) : MacroM Syntax :=
    let name        := expandIdentLiterally positionalArg[0]
    let type        := positionalArg[2]
    let description := positionalArg[4]
    `(Arg.mk $name $description $type)

  syntax variableArg := colGe "..." term " : " term "; " term

  def expandVariableArg (variableArg : Syntax) : MacroM Syntax := do
    let name        := expandIdentLiterally variableArg[1]
    let type        := variableArg[3]
    let description := variableArg[5]
    `(Arg.mk $name $description $type)

  syntax flag := colGe term ("," term)? (" : " term)? "; " term

  def expandFlag (flag : Syntax) : MacroM Syntax := do
    let (shortName, longName) :=
      if flag[1].isNone then
        (quote (none : Option String), expandIdentLiterally flag[0])
      else
        (expandIdentLiterally flag[0], expandIdentLiterally flag[1][1])
    let type        := if flag[2].isNone then ← `(Unit) else flag[2][1]
    let description := flag[4]
    `(Flag.mk $shortName $longName $description $type)

  syntax "`[Cli|\n"
      term " VIA " term "; " "[" term "]"
      term
      ("FLAGS:\n" withPosition((flag)*))?
      ("ARGS:\n" withPosition((positionalArg)* (variableArg)?))?
      ("SUBCOMMANDS: " sepBy(term, ";", "; "))?
      ("EXTENSIONS: " sepBy(term, ";", "; "))?
    "\n]" : term

  macro_rules
    | `(`[Cli|
        $name:term VIA $run:term; [$version:term]
        $description:term
        $[FLAGS:
          $flags*
        ]?
        $[ARGS:
          $positionalArgs*
          $[$variableArg]?
        ]?
        $[SUBCOMMANDS: $subCommands;*]?
        $[EXTENSIONS: $extensions;*]?
      ]) => do
        `(Cmd.mk
          (name           := $(expandIdentLiterally name))
          (version        := $version)
          (description    := $description)
          (flags          := $((← flags.getD #[] |>.mapM expandFlag) |> quote))
          (positionalArgs := $((← positionalArgs.getD #[] |>.mapM expandPositionalArg) |> quote))
          (variableArg?   := $((← variableArg.join.mapM expandVariableArg) |> quote))
          (run            := $run)
          (subCmds        := $(quote <| (subCommands.getD (#[] : Array Syntax) : Array Syntax)))
          (extension?     := some <| Array.foldl Extension.then { : Extension }
            $(quote <| (extensions.getD (#[] : Array Syntax) : Array Syntax))))
end Macro

section Info
  /-- Maximum width within which all formatted text should fit. -/
  def maxWidth                  : Nat := 80
  /-- Amount of spaces with which section content is indented. -/
  def indentation               : Nat := 4
  /-- Maximum width within which all formatted text should fit, after indentation. -/
  def maxIndentedWidth          : Nat := maxWidth - indentation
  /-- Formats `xs` by `String.optJoin`ing the components with a single space. -/
  def line  (xs : Array String) : String := " ".optJoin xs
  /-- Formats `xs` by `String.optJoin`ing the components with a newline `\n`. -/
  def lines (xs : Array String) : String := "\n".optJoin xs

  /--
  Renders a help section with the designated `title` and `content`.
  If `content = ""`, `emptyContentPlaceholder?` will be used instead.
  If `emptyContentPlaceholder? = none`, neither the title nor the content
  will be rendered.
  -/
  def renderSection
    (title                    : String)
    (content                  : String)
    (emptyContentPlaceholder? : Option String := none)
    : String :=
    let titleLine? : Option String := OptionM.run do
      if content = "" then
        return s!"{title}: {← emptyContentPlaceholder?}"
      else
        return s!"{title}:"
    lines #[
      titleLine?.optStr,
      content |>.wrapWordsAt! maxIndentedWidth |>.indent indentation
    ]

  /--
  Renders a table using `Array.renderTable!` and then renders a section with
  the designated `title` and the rendered table as content.
  -/
  def renderTable
    (title                  : String)
    (columns                : Array (String × String))
    (emptyTablePlaceholder? : Option String := none)
    : String :=
    let table := columns.renderTable! (maxWidth := maxIndentedWidth)
    renderSection title table emptyTablePlaceholder?

  namespace Cmd
    private def metaDataInfo (c : Cmd) : String :=
      lines #[
        s!"{c.fullName} [{c.version}]".wrapWordsAt! maxWidth,
        c.description.wrapWordsAt! maxWidth
      ]

    private def usageInfo (c : Cmd) : String :=
      let subCmdTitle? : Option String := if ¬c.subCmds.isEmpty then "[SUBCOMMAND]" else none
      let posArgNames  : String        := line <| c.positionalArgs.map (s!"<{·.name}>")
      let varArgName?  : Option String := OptionM.run do return s!"<{(← c.variableArg?).name}>..."
      let info := line #[c.fullName, subCmdTitle?.optStr, "[FLAGS]", posArgNames, varArgName?.optStr]
      renderSection "USAGE" info

    private def flagInfo (c : Cmd) : String :=
      let columns : Array (String × String) := c.flags.map fun flag =>
        let shortName?    : Option String := OptionM.run do return s!"-{← flag.shortName?}"
        let names         : String        := ", ".optJoin #[shortName?.optStr, s!"--{flag.longName}"]
        let type?         : Option String := if ¬ flag.isParamless then s!": {flag.type.name}" else none
        (line #[names, type?.optStr], flag.description)
      renderTable "FLAGS" columns (emptyTablePlaceholder? := "None")

    private def positionalArgInfo (c : Cmd) : String :=
      let args :=
        if let some variableArg := c.variableArg? then
          c.positionalArgs ++ #[variableArg]
        else
          c.positionalArgs
      args.map (fun arg => (line #[arg.name, s!": {arg.type.name}"], arg.description))
        |> renderTable "ARGS"

    private def subCommandInfo (c : Cmd) : String :=
      c.subCmds.map (fun subCmd => (subCmd.name, subCmd.description))
        |> renderTable "SUBCOMMANDS"

    /-- Renders the help for `c`. -/
    def help (c : Cmd) : String :=
      lines #[
        c.metaDataInfo,
        "\n" ++ c.usageInfo,
        "\n" ++ c.flagInfo,
        (if ¬c.positionalArgs.isEmpty ∨ c.hasVariableArg then "\n" else "") ++ c.positionalArgInfo,
        (if ¬c.subCmds.isEmpty then "\n" else "") ++ c.subCommandInfo,
        (if c.hasFurtherInformation then "\n" else "") ++ c.furtherInformation?.optStr
      ]

    /-- Renders an error for `c` with the designated message `msg`. -/
    def error (c : Cmd) (msg : String) : String :=
      lines #[
        msg.wrapWordsAt! maxWidth,
        s!"Run `{c.fullName} -h` for further information.".wrapWordsAt! maxWidth
      ]

    /-- Prints the help for `c`. -/
    def printHelp    (c : Cmd)                : IO Unit := IO.println c.help
    /-- Prints an error for `c` with the designated message `msg`. -/
    def printError   (c : Cmd) (msg : String) : IO Unit := IO.println <| c.error msg
    /-- Prints the version of `c`. -/
    def printVersion (c : Cmd)                : IO Unit := IO.println c.version
  end Cmd
end Info

section Parsing
  /-- Represents the exact representation of a flag as input by the user. -/
  structure InputFlag where
    /-- Flag name input by the user. -/
    name    : String
    /-- Whether the flag input by the user was a short one. -/
    isShort : Bool

  instance : ToString InputFlag where
    toString f :=
      let pre := if f.isShort then "-" else "--"
      s!"{pre}{f.name}"

  namespace ParseError
    /-- Kind of error that occured during parsing. -/
    inductive Kind
    | unknownFlag
      (inputFlag : InputFlag)
      (msg       : String :=
        s!"Unknown flag `{inputFlag}`.")
    | missingFlagArg
      (flag      : Flag)
      (inputFlag : InputFlag)
      (msg       : String :=
        s!"Missing argument for flag `{inputFlag}`.")
    | duplicateFlag
      (flag      : Flag)
      (inputFlag : InputFlag)
      (msg       : String :=
        let complementaryName? : Option String := OptionM.run do
          if inputFlag.isShort then
            return s!" (`--{flag.longName}`)"
          else
            return s!" (`-{← flag.shortName?}`)"
        s!"Duplicate flag `{inputFlag}`{complementaryName?.optStr}.")
    | redundantFlagArg
      (flag       : Flag)
      (inputFlag  : InputFlag)
      (inputValue : String)
      (msg        : String :=
        s!"Redundant argument `{inputValue}` for flag `{inputFlag}` that takes no arguments.")
    | invalidFlagType
      (flag       : Flag)
      (inputFlag  : InputFlag)
      (inputValue : String)
      (msg        : String :=
        s!"Invalid type of argument `{inputValue}` for flag `{inputFlag} : {flag.type.name}`.")
    | missingPositionalArg
      (arg : Arg)
      (msg : String :=
        s!"Missing positional argument `<{arg.name}>.`")
    | invalidPositionalArgType
      (arg      : Arg)
      (inputArg : String)
      (msg      : String :=
        s!"Invalid type of argument `{inputArg}` for positional argument `<{arg.name} : {arg.type.name}>`.")
    | redundantPositionalArg
      (inputArg : String)
      (msg      : String :=
        s!"Redundant positional argument `{inputArg}`.")
    | invalidVariableArgType
      (arg      : Arg)
      (inputArg : String)
      (msg      : String :=
        s!"Invalid type of argument `{inputArg}` for variable argument `<{arg.name} : {arg.type.name}>...`.")

    /-- Associated message of the error. -/
    def Kind.msg : Kind → String
    | unknownFlag              _     msg
    | missingFlagArg           _ _   msg
    | duplicateFlag            _ _   msg
    | redundantFlagArg         _ _ _ msg
    | invalidFlagType          _ _ _ msg
    | missingPositionalArg     _     msg
    | invalidPositionalArgType _ _   msg
    | redundantPositionalArg   _     msg
    | invalidVariableArgType   _ _   msg => msg
  end ParseError

  open ParseError in
  /-- Error that occured during parsing. Contains the command that the error occured in and the kind of the error. -/
  structure ParseError where
    /-- Command that the error occured in. -/
    cmd         : Cmd
    /-- Kind of error that occured. -/
    kind        : Kind

  private structure ParseState where
    idx                  : Nat
    cmd                  : Cmd
    parsedFlags          : Array Parsed.Flag
    parsedPositionalArgs : Array Parsed.Arg
    parsedVariableArgs   : Array Parsed.Arg

  private abbrev ParseM := ExceptT ParseError (ReaderT (Array String) (StateM ParseState))

  namespace ParseM
    open ParseError.Kind

    private def args                 : ParseM (Array String)      := read
    private def idx                  : ParseM Nat                 := do return (← get).idx
    private def cmd                  : ParseM Cmd                 := do return (← get).cmd
    private def parsedFlags          : ParseM (Array Parsed.Flag) := do return (← get).parsedFlags
    private def parsedPositionalArgs : ParseM (Array Parsed.Arg)  := do return (← get).parsedPositionalArgs
    private def parsedVariableArgs   : ParseM (Array Parsed.Arg)  := do return (← get).parsedVariableArgs
    private def peek?                : ParseM (Option String)     := do return (← args).get? (← idx)
    private def peekNext?            : ParseM (Option String)     := do return (← args).get? <| (← idx) + 1
    private def flag? (inputFlag : InputFlag) : ParseM (Option Flag) := do
      if inputFlag.isShort then
        return (← cmd).flagByShortName? inputFlag.name
      else
        return (← cmd).flag? inputFlag.name

    private def setIdx (idx : Nat) : ParseM Unit := do
      set { ← get with idx := idx }
    private def setCmd (c : Cmd) : ParseM Unit := do
      set { ← get with cmd := c }
    private def pushParsedFlag (parsedFlag : Parsed.Flag) : ParseM Unit := do
      set { ← get with parsedFlags := (← parsedFlags).push parsedFlag }
    private def pushParsedPositionalArg (parsedPositionalArg : Parsed.Arg) : ParseM Unit := do
      set { ← get with parsedPositionalArgs := (← parsedPositionalArgs).push parsedPositionalArg }
    private def pushParsedVariableArg (parsedVariableArg : Parsed.Arg) : ParseM Unit := do
      set { ← get with parsedVariableArgs := (← parsedVariableArgs).push parsedVariableArg }
    private def skip : ParseM Unit := do
      setIdx <| (← idx) + 1

    private def parseError (kind : ParseError.Kind) : ParseM ParseError := do return ⟨← cmd, kind⟩

    private partial def parseSubCmds : ParseM Unit := do
      let mut lastSubCmd ← cmd
      repeat 
        let some arg ← peek? 
          | break
        let some subCmd := lastSubCmd.subCmd? arg 
          | break
        skip
        lastSubCmd := subCmd
      setCmd lastSubCmd

    private def parseEndOfFlags : ParseM Bool := do
      let some arg ← peek?
        | return false
      if arg = "--" then
        skip
        return true
      return false

    private def readFlagContent? : ParseM (Option (String × Bool)) := do
      let some arg ← peek?
        | return none
      if arg = "--" ∨ arg = "-" then
        return none
      if arg.take 2 = "--" then
        return (arg.drop 2, false)
      if arg.take 1 = "-" then
        return (arg.drop 1, true)
      return none

    private def ensureFlagUnique (flag : Flag) (inputFlag : InputFlag) : ParseM Unit := do
      if (← parsedFlags).find? (·.flag.longName = flag.longName) |>.isSome then
        throw <| ← parseError <| duplicateFlag flag inputFlag

    private def ensureFlagWellTyped (flag : Flag) (inputFlag : InputFlag) (value : String) : ParseM Unit := do
      if ¬ flag.type.isValid value then
        throw <| ← parseError <| invalidFlagType flag inputFlag value

    private partial def readMultiFlag? : ParseM (Option (Array Parsed.Flag)) := do
      let some (flagContent, true) ← readFlagContent?
        | return none
      let some (parsedFlags : Array (String × Parsed.Flag)) ← loop flagContent Std.RBTree.empty
        | return none
      for (inputFlagName, parsedFlag) in parsedFlags do
        ensureFlagUnique parsedFlag.flag ⟨inputFlagName, true⟩
      skip
      return some <| parsedFlags.map (·.2)
    where
      loop (flagContent : String) (matched : Std.RBTree String compare)
        : ParseM (Option (Array (String × Parsed.Flag))) := do
        -- this is not tail recursive, but that's fine: `loop` will only recurse further if the corresponding
        -- flag has not been matched yet, meaning that this can only overflow if the application has an
        -- astronomical amount of short flags.
        if flagContent = "" then
          return some #[]
        let parsedFlagsCandidates : Array (Array (String × Parsed.Flag)) ←
          (← cmd).flags.filter (·.isParamless)
          |>.filter            (·.hasShortName)
          |>.filter            (·.shortName!.isPrefixOf flagContent)
          |>.filter            (¬ matched.contains ·.shortName!)
          |>.qsort             (·.shortName!.length > ·.shortName!.length)
          |>.filterMapM fun flag => do
            let inputFlagName := flagContent.take flag.shortName!.length
            let restContent   := flagContent.drop flag.shortName!.length
            let newMatched    := matched.insert flag.shortName!
            let some tail ← loop restContent newMatched
              | return none
            return some <| #[(inputFlagName, ⟨flag, ""⟩)] ++ tail
        return parsedFlagsCandidates.get? 0

    private def readEqFlag? : ParseM (Option Parsed.Flag) := do
      let some (flagContent, isShort) ← readFlagContent?
        | return none
      match flagContent.splitOn "=" with
      | [] => panic! "Cli.readEqFlag?: String.splitOn returned empty list"
      | [name] => return none
      | (flagName :: flagArg :: rest) =>
        let flagValue := "=".intercalate <| flagArg :: rest
        let inputFlag : InputFlag := ⟨flagName, isShort⟩
        let some flag ← flag? inputFlag
          | throw <| ← parseError <| unknownFlag inputFlag
        if flag.isParamless then
          throw <| ← parseError <| redundantFlagArg flag inputFlag flagValue
        ensureFlagUnique flag inputFlag
        ensureFlagWellTyped flag inputFlag flagValue
        skip
        return some ⟨flag, flagValue⟩

    private def readWsFlag? : ParseM (Option Parsed.Flag) := do
      let some (flagName, isShort) ← readFlagContent?
        | return none
      let some flagValue ← peekNext?
        | return none
      let inputFlag : InputFlag := ⟨flagName, isShort⟩
      let some flag ← flag? inputFlag
        | return none
      if flag.isParamless then
        return none
      ensureFlagUnique flag inputFlag
      ensureFlagWellTyped flag inputFlag flagValue
      skip; skip
      return some ⟨flag, flagValue⟩

    private def readPrefixFlag? : ParseM (Option Parsed.Flag) := do
        let some (flagContent, true) ← readFlagContent?
          | return none
        let some flag :=
            (← cmd).flags.filter (¬ ·.isParamless)
            |>.filter            (·.hasShortName)
            |>.filter            (·.shortName!.isPrefixOf flagContent)
            |>.filter            (·.shortName!.length < flagContent.length)
            |>.qsort             (·.shortName!.length > ·.shortName!.length)
            |>.get? 0
          | return none
        let flagName  := flag.shortName!
        let flagValue := flagContent.drop flagName.length
        let inputFlag : InputFlag := ⟨flagName, true⟩
        ensureFlagUnique flag inputFlag
        ensureFlagWellTyped flag inputFlag flagValue
        skip
        return some ⟨flag, flagValue⟩

    private def readParamlessFlag? : ParseM (Option Parsed.Flag) := do
      let some (flagName, isShort) ← readFlagContent?
        | return none
      let inputFlag : InputFlag := ⟨flagName, isShort⟩
      let some flag ← flag? inputFlag
        | throw <| ← parseError <| unknownFlag inputFlag
      if ¬ flag.isParamless then
        throw <| ← parseError <| missingFlagArg flag inputFlag
      ensureFlagUnique flag inputFlag
      skip
      return some ⟨flag, ""⟩

    private def parseFlag : ParseM Bool := do
      if let some parsedFlags ← readMultiFlag? then
        for parsedFlag in parsedFlags do
          pushParsedFlag parsedFlag
        return true
      let tryRead parse : OptionT ParseM Parsed.Flag := parse
      let some parsedFlag ←
          tryRead readEqFlag?     <|>
          tryRead readWsFlag?     <|>
          tryRead readPrefixFlag? <|>
          tryRead readParamlessFlag?
        | return false
      pushParsedFlag parsedFlag
      return true

    private def parsePositionalArg : ParseM Bool := do
      let some positionalArgValue ← peek?
        | return false
      let some positionalArg := (← cmd).positionalArgs.get? (← parsedPositionalArgs).size
        | return false
      if ¬ positionalArg.type.isValid positionalArgValue then
        throw <| ← parseError <| invalidPositionalArgType positionalArg positionalArgValue
      skip
      pushParsedPositionalArg ⟨positionalArg, positionalArgValue⟩
      return true

    private def parseVariableArg : ParseM Bool := do
      let some variableArgValue ← peek?
        | return false
      let some variableArg := (← cmd).variableArg?
        | throw <| ← parseError <| redundantPositionalArg variableArgValue
      if ¬ variableArg.type.isValid variableArgValue then
        throw <| ← parseError <| invalidVariableArgType variableArg variableArgValue
      skip
      pushParsedVariableArg ⟨variableArg, variableArgValue⟩
      return true

    private partial def parseArgs : ParseM Unit := do
      let mut parseEverythingAsArg := false
      let mut noEndOfInput := true
      while noEndOfInput do
        if ← (pure !parseEverythingAsArg) <&&> parseEndOfFlags then
          parseEverythingAsArg := true
        noEndOfInput := ← (pure !parseEverythingAsArg) <&&> parseFlag
                      <||> parsePositionalArg
                      <||> parseVariableArg

    private def parse (c : Cmd) (args : List String) : Except ParseError (Cmd × Parsed) :=
      parse' args.toArray |>.run' {
        idx                  := 0
        cmd                  := c
        parsedFlags          := #[]
        parsedPositionalArgs := #[]
        parsedVariableArgs   := #[]
      }
    where
      parse' : ParseM (Cmd × Parsed) := do
        parseSubCmds
        parseArgs
        let parsed : Parsed := {
          cmd            := (← cmd).meta
          flags          := ← parsedFlags
          positionalArgs := ← parsedPositionalArgs
          variableArgs   := ← parsedVariableArgs
        }
        if parsed.hasFlag "help" ∨ parsed.hasFlag "version" then
          return (← cmd, parsed)
        if (← parsedPositionalArgs).size < (← cmd).positionalArgs.size then
          throw <| ← parseError <| missingPositionalArg <| (← cmd).positionalArgs.get! (← parsedPositionalArgs).size
        return (← cmd, parsed)
  end ParseM

  namespace Cmd
    /--
    Parses `args` according to the specification provided in `c`, returning either a `ParseError` or the
    (sub)command that was called and the parsed content of the input.
    Note that `args` designates the list `<foo>` in `somebinary <foo>`.
    -/
    def parse (c : Cmd) (args : List String) : Except ParseError (Cmd × Parsed) :=
      ParseM.parse c args

    /--
    Processes `args` by `Cmd.parse?`ing the input according to `c` and then applying the extension of the
    respective (sub)command that was called.
    Note that `args` designates the list `<foo>` in `somebinary <foo>`.
    Returns either the (sub)command that an error occured in and the corresponding error message or
    the (sub)command that was called and the parsed input after postprocessing.
    -/
    def process (c : Cmd) (args : List String) : Except (Cmd × String) (Cmd × Parsed) := do
      let result := c.parse args
      match result with
      | .ok (cmd, parsed) =>
        match cmd.extension? with
        | some ext =>
          let newMeta := ext.extendMeta cmd.meta
          let newCmd := cmd.update' (meta := newMeta)
          match ext.postprocess newMeta parsed with
          | .ok newParsed =>
            return (newCmd, newParsed)
          | .error msg =>
            throw (newCmd, msg)
        | none =>
          return (cmd, parsed)
      | .error err =>
        throw (err.cmd, err.kind.msg)
  end Cmd
end Parsing

section IO
  namespace Cmd
    /--
    Validates `args` by `Cmd.process?`ing the input according to `c`.
    Note that `args` designates the list `<foo>` in `somebinary <foo>`.
    Prints the help or the version of the called (sub)command if the respective flag was passed and
    returns `0` for the exit code.
    If neither of these flags were passed and processing was successful, the `run` handler of the
    called command is executed.
    In the case of a processing error, the error is printed and an exit code of `1` is returned.
    -/
    def validate (c : Cmd) (args : List String) : IO UInt32 := do
      let result := c.process args
      match result with
      | .ok (cmd, parsed) =>
        if parsed.hasFlag "help" then
          cmd.printHelp
          return 0
        if parsed.hasFlag "version" then
          cmd.printVersion
          return 0
        cmd.run parsed
      | .error (cmd, err) =>
        cmd.printError err
        return 1
  end Cmd
end IO

end Cli