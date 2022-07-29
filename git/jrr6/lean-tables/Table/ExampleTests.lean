import Table.API
import Table.ExampleTables
import Table.Notation

-- Table equality typeclass resolution requires a lot of instances
set_option synthInstance.maxSize 12000
set_option synthInstance.maxHeartbeats 0

-- TODO: come up with a better testing system
-- Modified version of `elabEvalUnsafe` (src/lean/lean/elab/builtincommand.lean)
syntax (name := test) "#test" term : command
@[commandElab test]
unsafe def elabTest : Lean.Elab.Command.CommandElab
| `(#test%$tk $term) => do
    let n := `_eval
    let ctx ← read
    let addAndCompile (value : Lean.Expr) : Lean.Elab.TermElabM Unit := do
      -- the type really should be `Bool` at this point (b/c of `mkDecide`)
      -- (but could enforcing that explicitly lead to less-graceful failures?)
      let type ← Lean.Meta.inferType value
      let us := Lean.collectLevelParams {} value |>.params
      -- let value ← Lean.Meta.instantiateMVars value
      let decl := Lean.Declaration.defnDecl {
        name        := n
        levelParams := us.toList
        type        := type
        value       := value
        hints       := Lean.ReducibilityHints.opaque
        safety      := Lean.DefinitionSafety.unsafe
      }
      Lean.Elab.Term.ensureNoUnassignedMVars decl
      Lean.addAndCompile decl
    let elabEvalTerm : Lean.Elab.TermElabM Lean.Expr := do
      let ebool ← Lean.Elab.Term.elabTerm (← `(Bool)) none
      let e ← Lean.Elab.Term.elabTerm term none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing

      -- Need to do this here so we can ensure the type is correct and return
      -- a meaningful error message otherwise
      let (e, _) ← Lean.Elab.Term.levelMVarToParam
                    (← Lean.Meta.instantiateMVars e)
      let e_type ← Lean.Meta.inferType e
      if (← Lean.Meta.isProp e) then
        Lean.Meta.mkDecide e
      else if (← Lean.Meta.isDefEq e_type ebool) then
        return e
      else
        throwError m!"Tests must be of type Bool or Prop, but got '{e_type}'"
    let elabEval : Lean.Elab.Command.CommandElabM Unit :=
    Lean.Elab.Command.runTermElabM (some n) (λ _ => do
      let e ← elabEvalTerm
      let env ← Lean.getEnv
      let res ← try addAndCompile e; Lean.evalConst Bool n
                finally Lean.setEnv env
      if res
      then Lean.Elab.logInfoAt tk "Test passed"
      else Lean.Elab.logErrorAt tk "Test failed")
    elabEval
| _ => Lean.Elab.throwUnsupportedSyntax

-- Ways of making type class inference work where Lean struggles
def instHint (α : Type _) (x : α) (y : α) (inst : DecidableEq α) :=
  decide (x = y)

macro "inst" : tactic =>
  `(repeat (first
    | apply instDecidableEqTable (inst := _)
    | apply instDecidableEqRowConsHeaderMkType (it := _) (ic := _) (ir := _)
    | apply instDecidableEqRowNilHeader
    | apply instDecidableEqCell (inst := _)
    | infer_instance))

notation lhs "=(" tp ")" rhs => instHint tp lhs rhs inferInstance

notation lhs "=[" inst "]" rhs => instHint _ lhs rhs inst

notation lhs "=(" tp ")[" inst "]" rhs => instHint tp lhs rhs inst

-- `addRows`
#test
addRows students [/["Colton", 19, "blue"]]
=
Table.mk [
  /["Bob"  , 12, "blue" ],
  /["Alice", 17, "green"],
  /["Eve"  , 13, "red"  ],
  /["Colton", 19, "blue"]
]

#test
addRows gradebook []
=
Table.mk [
  /["Bob"  , 12, 8, 9, 77, 7, 9, 87],
  /["Alice", 17, 6, 8, 88, 8, 7, 85],
  /["Eve"  , 13, 7, 9, 84, 8, 8, 77]
]

-- `addColumn`
def hairColor := [some "brown", some "red", some "blonde"]
#test
addColumn students "hair-color" hairColor
=[by inst]
Table.mk [
  /[ "Bob"   , 12  , "blue"         , "brown"    ],
  /[ "Alice" , 17  , "green"        , "red"      ],
  /[ "Eve"   , 13  , "red"          , "blonde"   ]
]

def presentation := [some 9, some 9, some 6]
#test
addColumn gradebook "presentation" presentation
=[by inst]
Table.mk [
  /[ "Bob"  , 12, 8, 9, 77, 7, 9, 87, 9],
  /[ "Alice", 17, 6, 8, 88, 8, 7, 85, 9],
  /[ "Eve"  , 13, 7, 9, 84, 8, 8, 77, 6]
]

-- `buildColumn`
def isTeenagerBuilder := λ (r : Row $ schema students) =>
  match getValue r "age" (by header) with
  | some age => some (12 < age && age < 20)
  | _ => some false
#test
buildColumn students "is-teenager" isTeenagerBuilder
=[by inst]
Table.mk [
  /[ "Bob"   , 12  , "blue"         , false       ],
  /[ "Alice" , 17  , "green"        , true        ],
  /[ "Eve"   , 13  , "red"          , true        ]
]

def didWellOnFinal : Row (schema gradebook) → Option Bool := λ r =>
  match getValue r "final" (by header) with
  | some score => some $ 85 <= score
  | _ => some false
#test
buildColumn gradebook "did-well-on-final" didWellOnFinal
=[by inst]
Table.mk [
  /[ "Bob"  , 12, 8, 9, 77, 7, 9, 87, true ],
  /[ "Alice", 17, 6, 8, 88, 8, 7, 85, true ],
  /[ "Eve"  , 13, 7, 9, 84, 8, 8, 77, false]
]

-- `vcat`
def increaseAge := λ (r : Row $ schema students) =>
  ((
    Row.cons
      (Cell.fromOption $ (getValue r "age" (by header)).map (λ x => x + 1))
      Row.nil
  )
  : Row [("age", Nat)])

#test
vcat students (update [⟨("age", Nat), by header⟩] students increaseAge)
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Alice" , 17  , "green"        ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Bob"   , 13  , "blue"         ],
  /[ "Alice" , 18  , "green"        ],
  /[ "Eve"   , 14  , "red"          ]
]

def curveMidtermAndFinal := λ (r : Row $ schema gradebook) =>
  let curve := λ | some n => some (n + 5)
                 | _ => none
  let midterm := getValue r "midterm" (by header)
  let final := getValue r "final" (by header)
  (Row.cons (Cell.fromOption $ curve midterm) $
     Row.cons (Cell.fromOption $ curve final) Row.nil
   : Row [("midterm", Nat), ("final", Nat)])

#test
vcat gradebook (update [⟨("midterm", Nat), by header⟩,  
                        ⟨("final", Nat), by header⟩] gradebook
                                                     curveMidtermAndFinal)
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ],
  /[ "Bob"   , 12  , 8     , 9     , 82      , 7     , 9     , 92    ],
  /[ "Alice" , 17  , 6     , 8     , 93      , 8     , 7     , 90    ],
  /[ "Eve"   , 13  , 7     , 9     , 89      , 8     , 8     , 82    ]
]

-- `hcat`
-- TODO: don't have `dropColumns` yet

-- `values`
#test
values [/["Alice"], /["Bob"]]
=
(Table.mk [
  /["Alice"],
  /["Bob"]
] : Table [("name", String)])

#test
values [/["Alice", 12], /["Bob", 13]]
=
(Table.mk [
  /["Alice", 12],
  /["Bob", 13]
] : Table [("name", String), ("age", Nat)])

-- `crossJoin`
def petiteJelly :=
selectRows1 (selectColumns2 jellyAnon [⟨0, by simp⟩, ⟨1, by simp⟩, ⟨2, by simp⟩])
            [⟨0, by simp⟩, ⟨1, by simp⟩]
#test
crossJoin students petiteJelly
=[by simp [List.nth, List.nths, List.map]; inst]
Table.mk [
  /[ "Bob"   , 12  , "blue"         , true     , false , false ],
  /[ "Bob"   , 12  , "blue"         , true     , false , true  ],
  /[ "Alice" , 17  , "green"        , true     , false , false ],
  /[ "Alice" , 17  , "green"        , true     , false , true  ],
  /[ "Eve"   , 13  , "red"          , true     , false , false ],
  /[ "Eve"   , 13  , "red"          , true     , false , true  ]
]

#test
crossJoin emptyTable petiteJelly
=[by simp [List.nth, List.nths, List.map]; inst]
Table.mk []

-- TODO: `leftJoin`

-- `nrows`
#test nrows (@emptyTable String _) = 0

#test nrows studentsMissing = 3

-- `ncols`
#test ncols students = 3

#test ncols studentsMissing = 3

-- `header`
#test header students = ["name", "age", "favorite color"]

#test
header gradebook
=
["name", "age", "quiz1", "quiz2", "midterm", "quiz3", "quiz4", "final"]

-- `getRow`
#test
getRow students 0 (by simp)
=
/["Bob", 12, "blue"]

#test
getRow gradebook 1 (by simp)
=
/["Alice", 17, 6, 8, 88, 8, 7, 85]

-- `getValue`
#test
getValue /["name" := "Bob", "age" := 12] "name" (by header)
=
some "Bob"

#test
getValue /["name" := "Bob", "age" := 12] "age" (by header)
=
some 12

-- `getColumn1`
#test
getColumn1 students 1 (by simp)
=(List $ Option Nat)
[some 12, some 17, some 13]

#test
getColumn1 gradebook 0 (by simp)
=(List $ Option String)
[some "Bob", some "Alice", some "Eve"]

-- `getColumn2`
#test
getColumn2 students "age" (by header)
=
[some 12, some 17, some 13]

#test
getColumn2 gradebook "name" (by header)
=
[some "Bob", some "Alice", some "Eve"]

-- `selectRows1`
#test
selectRows1 students [⟨2, by simp⟩, ⟨0, by simp⟩, ⟨2, by simp⟩, ⟨1, by simp⟩]
=
Table.mk [
  /[ "Eve"   , 13  , "red"          ],
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

#test
selectRows1 gradebook [⟨2, by simp⟩, ⟨1, by simp⟩]
=
Table.mk [
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ]
]

-- `selectRows2`
#test
selectRows2 students [true, false, true] (by simp)
=
Table.mk [
  /[ "Bob" , 12  , "blue"         ],
  /[ "Eve" , 13  , "red"          ]
]

#test
selectRows2 gradebook [false, false, true] (by simp)
=
Table.mk [/["Eve", 13, 7, 9, 84, 8, 8, 77]]

-- `selectColumns1`
#test
selectColumns1 students [true, true, false] (by simp)
=[by inst]
Table.mk [
  /[ "Bob"   , 12  ],
  /[ "Alice" , 17  ],
  /[ "Eve"   , 13  ]
]

#test
selectColumns1 gradebook [true, false, false, false, true, false, false, true] (by simp)
=[by inst]
Table.mk [
  /[ "Bob"   , 77      , 87    ],
  /[ "Alice" , 88      , 85    ],
  /[ "Eve"   , 84      , 77    ]
]

-- `selectColumns2`
#test
selectColumns2 students [⟨2, by simp⟩, ⟨1, by simp⟩]
=(Table [("favorite color", String), ("age", Nat)])
Table.mk [
  /[ "blue"         , 12  ],
  /[ "green"        , 17  ],
  /[ "red"          , 13  ]
]

#test
selectColumns2 gradebook [⟨7, by simp⟩, ⟨0, by simp⟩, ⟨4, by simp⟩]
=(Table [(_, Nat), (_, String), (_, Nat)])
Table.mk [
  /[ 87    , "Bob"   , 77      ],
  /[ 85    , "Alice" , 88      ],
  /[ 77    , "Eve"   , 84      ]
]

-- `selectColumns3`
#test
selectColumns3 students [⟨("favorite color", _), by header⟩, ⟨("age", _), by header⟩]
=(Table [("favorite color", String), ("age", Nat)])
Table.mk [
  /[ "blue"         , 12  ],
  /[ "green"        , 17  ],
  /[ "red"          , 13  ]
]

#test
selectColumns3 gradebook [⟨("final", _), by header⟩, ⟨("name", _), by header⟩, ⟨("midterm", _), by header⟩]
=(Table [("final", Nat), ("name", String), ("midterm", Nat)])
Table.mk [
  /[ 87    , "Bob"   , 77      ],
  /[ 85    , "Alice" , 88      ],
  /[ 77    , "Eve"   , 84      ]
]

-- `head`
#test
head students ⟨1, by simp⟩
=
Table.mk [ /["Bob", 12, "blue"]]

#test
head students ⟨-2, by simp⟩
=
Table.mk [ /["Bob", 12, "blue"]]

-- `distinct`
#test
distinct students
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Alice" , 17  , "green"        ],
  /[ "Eve"   , 13  , "red"          ]
]

#test
distinct (selectColumns3 gradebook [⟨("quiz3", _), by header⟩])
=(Table [("quiz3", Nat)])
Table.mk [ /[7], /[8] ]

-- `dropColumn`
#test
dropColumn students ⟨"age", by name⟩
=(Table [("name", String), ("favorite color", String)])
Table.mk [
  /[ "Bob"   , "blue"         ],
  /[ "Alice" , "green"        ],
  /[ "Eve"   , "red"          ]
]

#test
dropColumn gradebook ⟨"final", by name⟩
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     ]
]

-- `dropColumns`
#test
dropColumns students A[⟨"age", by name⟩]
=(Table [("name", String), ("favorite color", String)])
Table.mk [
  /[ "Bob"   , "blue"         ],
  /[ "Alice" , "green"        ],
  /[ "Eve"   , "red"          ]
]

#test
dropColumns gradebook A[⟨"final", by name⟩, ⟨"midterm", by name⟩]
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 7     , 9     ],
  /[ "Alice" , 17  , 6     , 8     , 8     , 7     ],
  /[ "Eve"   , 13  , 7     , 9     , 8     , 8     ]
]

-- `tfilter`
def ageUnderFifteen : (Row $ schema students) → Bool := λ r =>
  match getValue r "age" (by header) with
  | some a => a < 15
  | _ => false

#test
tfilter students ageUnderFifteen
=
Table.mk [
  /[ "Bob" , 12  , "blue"         ],
  /[ "Eve" , 13  , "red"          ]
]

def nameLongerThan3Letters : (Row $ schema gradebook) → Bool := λ r =>
  match getValue r "name" (by header) with
  | some name => String.length name > 3
  | _ => false

#test
tfilter gradebook nameLongerThan3Letters
=
Table.mk [/["Alice", 17, 6, 8, 88, 8, 7, 85]]

-- `tsort`
#test
tsort students ⟨"age", by header⟩ true
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

#test
tsort gradebook ⟨"final", by header⟩ false
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ]
]

-- `sortByColumns`
#test
sortByColumns students [⟨("age", Nat), by header, inferInstance⟩]
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

#test
sortByColumns gradebook [⟨("quiz2", Nat), by header, inferInstance⟩,
                         ⟨("quiz1", Nat), by header, inferInstance⟩]
=
Table.mk [
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ],
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ]
]

-- `orderBy`
def nameLengthOB (r : Row $ schema students) :=
  match getValue r "name" (by header) with
  | some s => String.length s
  | _ => 0

def leOB := (λ (a : Nat) b => decide $ a ≤ b)

#test
orderBy students [⟨_, nameLengthOB, leOB⟩]
=
Table.mk [
  /[ "Bob"   , 12  , "blue"         ],
  /[ "Eve"   , 13  , "red"          ],
  /[ "Alice" , 17  , "green"        ]
]

def geOB := (λ (a : Nat) b => decide $ a ≥ b)

def nameLengthOB' (r : Row $ schema gradebook) :=
  match getValue r "name" (by header) with
  | some s => String.length s
  | _ => 0

def averageOB (xs : List $ Option Nat) :=
  List.foldl (λ acc => λ | none => acc | some x => x + acc) 0 xs / xs.length

def midtermAndFinalOB (r : Row $ schema gradebook) : List $ Option Nat :=
  [getValue r "midterm" (by header), getValue r "final" (by header)]

def compareGradeOB (g1 : List $ Option Nat) (g2 : List $ Option Nat) :=
  leOB (averageOB g1) (averageOB g2)

#test
orderBy gradebook [⟨_, nameLengthOB', geOB⟩, ⟨_, midtermAndFinalOB, compareGradeOB⟩]
=
Table.mk [
  /[ "Alice" , 17  , 6     , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 84      , 8     , 8     , 77    ],
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ]
]

-- `count`
#test
count students ⟨"favorite color", by header⟩
=
Table.mk [
  /[ "blue"  , 1     ],
  /[ "green" , 1     ],
  /[ "red"   , 1     ]
]

#test
count gradebook ⟨"age", by header⟩
=
Table.mk [
  /[ 12    , 1     ],
  /[ 17    , 1     ],
  /[ 13    , 1     ]
]

-- `bin`
#test
bin students ⟨"age", by header⟩ ⟨5, by simp⟩
=
Table.mk [
  /[ "10 <= age < 15" , 2     ],
  /[ "15 <= age < 20" , 1     ]
]

-- TODO: tell B2T2 that there's a typo in this test ("final," not "age")
#test
bin gradebook ⟨"final", by header⟩ ⟨5, by simp⟩
=
Table.mk [
  /[ "75 <= final < 80" , 1     ],
  /[ "80 <= final < 85" , 0     ],
  /[ "85 <= final < 90" , 2     ]
]

-- `pivotTable`
def oAverage (xs : List $ Option Nat) : Option Nat := some $
  List.foldl (λ acc => λ | none => acc | some x => x + acc) 0 xs / xs.length

#test
pivotTable students [⟨("favorite color", _), by header⟩] (by inst) [⟨("age-average", _), ⟨("age", _), by header⟩, oAverage⟩]
=[by inst]
Table.mk [
  /[ "blue"         , 12          ],
  /[ "green"        , 17          ],
  /[ "red"          , 13          ]
]

-- Slightly modified since we aren't using decimals
def proportion (bs : List $ Option Bool) : Option Nat := some $
  (100 * (bs.filter (λ | some true => true | _ => false)).length) / bs.length

-- TODO: does order matter?
#test
pivotTable
  jellyNamed
  [⟨("get acne", Bool), by header⟩, ⟨("brown", _), by header⟩]
  (by inst)
  [⟨("red-proportion", _), ⟨("red", _), by header⟩, proportion⟩,
   ⟨("pink-proportion", _), ⟨("pink", _), by header⟩, proportion⟩]
=[by inst]
Table.mk [
  /[ false    , false , 0              , 75              ],
  /[ false    , true  , 100            , 100             ],
  /[ true     , false , 0              , 25              ],
  /[ true     , true  , 0              , 0               ]
]

-- `groupBy`
-- TODO: handle `none` case?
def colorTemp : (Row $ schema students) → String := λ r =>
  match getValue r "favorite color" (by header) with
  | some "red" => "warm"
  | _ => "cool"

def nameLength : (Row $ schema students) → Nat := λ r =>
  match getValue r "name" (by header) with
  | some s => String.length s
  | _ => 0

def average (xs : List Nat) := List.foldl (·+·) 0 xs / xs.length

def aggregate := λ (k : String) vs =>
/["key" := k, "average" := average vs]

-- TODO: Need to double-check, but this seems to me like the correct output --
-- the first row matches "cool," so order preservation would tell us that this
-- order (and not the reversed order in the B2T2 docs) is most reasonable
-- (B2T2 TS is using unordered maps in the implementation of `groupBy`, which is
-- probably why its order is different)
#test
groupBy students colorTemp nameLength aggregate
=
Table.mk [
  /[ "cool" , 4       ],
  /[ "warm" , 3       ]
]

def abstractAge := λ (r : Row $ schema gradebook) =>
  match getValue r "age" (by header) with
  | some age =>
    match (age ≤ 12 : Bool), (age ≤ 19 : Bool) with
    | true, _ => "kid"
    | _, true => "teenager"
    | _, _ => "adult"
  | _ => ""

def finalGrade := λ (r : Row $ schema gradebook) =>
  match getValue r "final" (by header) with
  | some grade => grade
  | _ => 0

#test
groupBy gradebook abstractAge finalGrade aggregate
=
Table.mk [
  /[ "kid"      , 87      ],
  /[ "teenager" , 81      ]
]

-- `completeCases`
#test
completeCases students ⟨"age", by header⟩
=
[true, true, true]

#test
completeCases studentsMissing ⟨"age", by header⟩
=
[false, true, true]

-- `dropna`
#test
dropna studentsMissing
=
Table.mk [/["Alice", 17, "green"]]

#test
dropna gradebookMissing
=
Table.mk [/["Bob", 12, 8, 9, 77, 7, 9, 87]]

-- `fillna`
#test
fillna studentsMissing ⟨"favorite color", by header⟩ "white"
=
Table.mk [
  /[ "Bob"   , EMP, "blue"],
  /[ "Alice" , 17 , "green"],
  /[ "Eve"   , 13 , "white"]
]

#test
fillna gradebookMissing ⟨"quiz1", by header⟩ 0
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 88      , EMP   , 7     , 85    ],
  /[ "Eve"   , 13  , 0     , 9     , 84      , 8     , 8     , 77    ]
]

-- `pivotLonger`
-- TODO: more typeclass issues...
#test
pivotLonger gradebook A[⟨"midterm", by header⟩, ⟨"final", by header⟩] "exam" "score"
=[by simp [Schema.removeTypedNames, Schema.removeTypedName, Schema.removeHeader, Schema.removeName]; inst]
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 7     , 9     , "midterm" , 77    ],
  /[ "Bob"   , 12  , 8     , 9     , 7     , 9     , "final"   , 87    ],
  /[ "Alice" , 17  , 6     , 8     , 8     , 7     , "midterm" , 88    ],
  /[ "Alice" , 17  , 6     , 8     , 8     , 7     , "final"   , 85    ],
  /[ "Eve"   , 13  , 7     , 9     , 8     , 8     , "midterm" , 84    ],
  /[ "Eve"   , 13  , 7     , 9     , 8     , 8     , "final"   , 77    ]
]

#test
pivotLonger gradebook A[⟨"quiz1", by header⟩, ⟨"quiz2", by header⟩,
                        ⟨"quiz3", by header⟩, ⟨"quiz4", by header⟩,
                        ⟨"midterm", by header⟩, ⟨"final", by header⟩]
            "test" "score"
=
Table.mk [
  /[ "Bob"   , 12  , "quiz1"   , 8     ],
  /[ "Bob"   , 12  , "quiz2"   , 9     ],
  /[ "Bob"   , 12  , "quiz3"   , 7     ],
  /[ "Bob"   , 12  , "quiz4"   , 9     ],
  /[ "Bob"   , 12  , "midterm" , 77    ],
  /[ "Bob"   , 12  , "final"   , 87    ],
  /[ "Alice" , 17  , "quiz1"   , 6     ],
  /[ "Alice" , 17  , "quiz2"   , 8     ],
  /[ "Alice" , 17  , "quiz3"   , 8     ],
  /[ "Alice" , 17  , "quiz4"   , 7     ],
  /[ "Alice" , 17  , "midterm" , 88    ],
  /[ "Alice" , 17  , "final"   , 85    ],
  /[ "Eve"   , 13  , "quiz1"   , 7     ],
  /[ "Eve"   , 13  , "quiz2"   , 9     ],
  /[ "Eve"   , 13  , "quiz3"   , 8     ],
  /[ "Eve"   , 13  , "quiz4"   , 8     ],
  /[ "Eve"   , 13  , "midterm" , 84    ],
  /[ "Eve"   , 13  , "final"   , 77    ]
]

-- TODO: `pivotWider`

-- `flatten`
#test
flatten gradebookSeq A[⟨"quizzes", _, by header⟩]
=(Table [("name", String), ("age", Nat), ("quizzes", Nat), ("midterm", Nat), ("final", Nat)])
Table.mk [
  /[ "Bob"   , 12  , 8       , 77      , 87    ],
  /[ "Bob"   , 12  , 9       , 77      , 87    ],
  /[ "Bob"   , 12  , 7       , 77      , 87    ],
  /[ "Bob"   , 12  , 9       , 77      , 87    ],
  /[ "Alice" , 17  , 6       , 88      , 85    ],
  /[ "Alice" , 17  , 8       , 88      , 85    ],
  /[ "Alice" , 17  , 8       , 88      , 85    ],
  /[ "Alice" , 17  , 7       , 88      , 85    ],
  /[ "Eve"   , 13  , 7       , 84      , 77    ],
  /[ "Eve"   , 13  , 9       , 84      , 77    ],
  /[ "Eve"   , 13  , 8       , 84      , 77    ],
  /[ "Eve"   , 13  , 8       , 84      , 77    ]
]

def t := buildColumn gradebookSeq "quiz-pass?" (λ r => 
  let isPass : Nat → Bool := λ n => n >= 8
  (getValue r "quizzes" (by header)).map (List.map isPass)
)

-- FIXME: flatten is implemented incorrectly
#test
flatten t A[⟨"quiz-pass?", _, by header⟩, ⟨"quizzes", _, by header⟩]
=
Table.mk [
  /[ "Bob"   , 12  , 8       , 77      , 87    , true       ],
  /[ "Bob"   , 12  , 9       , 77      , 87    , true       ],
  /[ "Bob"   , 12  , 7       , 77      , 87    , false      ],
  /[ "Bob"   , 12  , 9       , 77      , 87    , true       ],
  /[ "Alice" , 17  , 6       , 88      , 85    , false      ],
  /[ "Alice" , 17  , 8       , 88      , 85    , true       ],
  /[ "Alice" , 17  , 8       , 88      , 85    , true       ],
  /[ "Alice" , 17  , 7       , 88      , 85    , false      ],
  /[ "Eve"   , 13  , 7       , 84      , 77    , false      ],
  /[ "Eve"   , 13  , 9       , 84      , 77    , true       ],
  /[ "Eve"   , 13  , 8       , 84      , 77    , true       ],
  /[ "Eve"   , 13  , 8       , 84      , 77    , true       ]
]

-- FIXME: more typeclass issues
-- `transformColumn`
def addLastName := Option.map (· ++ " Smith")

#test
transformColumn students ⟨"name", by header⟩ addLastName
=(Table [("name", String), ("age", Nat), ("favorite color", String)])
Table.mk [
  /[ "Bob Smith"   , 12  , "blue"         ],
  /[ "Alice Smith" , 17  , "green"        ],
  /[ "Eve Smith"   , 13  , "red"          ]
]

def quizScoreToPassFail := Option.map (λ n =>
  if n <= 6
  then "fail"
  else "pass")

#test
transformColumn gradebook ⟨"quiz1", by header⟩ quizScoreToPassFail
=
Table.mk [
  /[ "Bob"   , 12  , "pass" , 9     , 77      , 7     , 9     , 87    ],
  /[ "Alice" , 17  , "fail" , 8     , 88      , 8     , 7     , 85    ],
  /[ "Eve"   , 13  , "pass" , 9     , 84      , 8     , 8     , 77    ]
]

-- `renameColumns`
#test
renameColumns students A[⟨⟨"favorite color", by name⟩, "preferred color"⟩,
                         ⟨⟨"name", by name⟩, "first name"⟩]
=(Table [("first name", String), ("age", Nat), ("preferred color", String)])
Table.mk [
  /[ "Bob"      , 12  , "blue"          ],
  /[ "Alice"    , 17  , "green"         ],
  /[ "Eve"      , 13  , "red"           ]
]

#test
renameColumns gradebook A[⟨⟨"midterm", by name⟩, "final"⟩,
                          ⟨⟨"final", by name⟩, "midterm"⟩]
=(Table [("name", String), ("age", Nat), ("quiz1", Nat), ("quiz2", Nat),
         ("final", Nat), ("quiz3", Nat), ("quiz4", Nat), ("final", Nat)])
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , 77    , 7     , 9     , 87      ],
  /[ "Alice" , 17  , 6     , 8     , 88    , 8     , 7     , 85      ],
  /[ "Eve"   , 13  , 7     , 9     , 84    , 8     , 8     , 77      ]
]

-- `find`
#test
find students /["age" := 13]
=
some 2

#test
find students /["age" := 14]
=
none

-- `groupByRetentive`
-- Deal with ULift decidable equality
deriving instance DecidableEq for ULift

#test
groupByRetentive students ⟨"favorite color", by header⟩
=
Table.mk [
  /[ULift.up "blue" , Table.mk [
                        /["Bob"  , 12, "blue" ]]],
  /[ULift.up "green", Table.mk [
                        /["Alice", 17, "green"]]],
  /[ULift.up "red"  , Table.mk [
                        /["Eve"  , 13, "red"  ]]]
]

#test
groupByRetentive jellyAnon ⟨"brown", by header⟩
=[by inst]
Table.mk [
  /[ULift.up false, Table.mk [
    /[ true     , false , false , false , true  , false  , false , true   , false , false  ],
    /[ true     , false , true  , false , true  , true   , false , false  , false , false  ],
    /[ false    , false , false , false , true  , false  , false , false  , true  , false  ],
    /[ false    , false , false , false , false , true   , false , false  , false , false  ],
    /[ false    , false , false , false , false , true   , false , false  , true  , false  ],
    /[ true     , false , true  , false , false , false  , false , true   , true  , false  ],
    /[ false    , false , true  , false , false , false  , false , false  , true  , false  ],
    /[ true     , false , false , false , false , false  , false , true   , false , false  ]
  ]],
  /[ULift.up true, Table.mk [
    /[ true     , false , false , false , false , false  , true  , true   , false , false  ],
    /[ false    , true  , false , false , false , true   , true  , false  , true  , false  ]
  ]]
]

-- `groupBySubtractive`
-- TODO: why does the `header` tactic fail here?
-- Interestingly, only fails when we have the equality test -- evaluating
-- `groupBySubtractive` alone works just fine
#test
groupBySubtractive students ⟨"favorite color", Schema.HasCol.tl (Schema.HasCol.tl (Schema.HasCol.hd))⟩
=[by inst]
Table.mk [
  /[ULift.up "blue" , Table.mk [/["Bob"  , 12]]],
  /[ULift.up "green", Table.mk [/["Alice", 17]]],
  /[ULift.up "red", Table.mk [/["Eve"  , 13]]]
]

#test
groupBySubtractive jellyAnon ⟨"brown",
  Schema.HasCol.tl $ Schema.HasCol.tl $ Schema.HasCol.tl $ Schema.HasCol.tl $
    Schema.HasCol.tl $ Schema.HasCol.tl $ Schema.HasCol.hd⟩
=[by inst]
Table.mk [
  /[ULift.up false, Table.mk [
    /[ true     , false , false , false , true  , false  , true   , false , false  ],
    /[ true     , false , true  , false , true  , true   , false  , false , false  ],
    /[ false    , false , false , false , true  , false  , false  , true  , false  ],
    /[ false    , false , false , false , false , true   , false  , false , false  ],
    /[ false    , false , false , false , false , true   , false  , true  , false  ],
    /[ true     , false , true  , false , false , false  , true   , true  , false  ],
    /[ false    , false , true  , false , false , false  , false  , true  , false  ],
    /[ true     , false , false , false , false , false  , true   , false , false  ]
  ]],
  /[ULift.up true, Table.mk [
    /[ true     , false , false , false , false , false  , true   , false , false  ],
    /[ false    , true  , false , false , false , true   , false  , true  , false  ]
  ]]
]

-- `update`
def abstractAgeUpdate := λ (r : Row $ schema students) =>
  match getValue r "age" (by header) with
  | some age =>
    match (age ≤ 12 : Bool), (age ≤ 19 : Bool) with
    | true, _ => /["age" := "kid"]
    | _, true => /["age" := "teenager"]
    | _, _ => /["age" := "adult"]
  | _ => /["age" := EMP]

#test
update [⟨("age", String), _⟩] students abstractAgeUpdate
=(Table [("name", String), ("age", String), ("favorite color", String)])
Table.mk [
  /[ "Bob"   , "kid"      , "blue"         ],
  /[ "Alice" , "teenager" , "green"        ],
  /[ "Eve"   , "teenager" , "red"          ]
]

def didWellUpdate := λ (r : Row $ schema gradebook) =>
  match getValue r "midterm" (by header), getValue r "final" (by header) with
  | some (m : Nat), some (f : Nat) => /["midterm" := (85 ≤ m : Bool), "final" := (85 ≤ f : Bool)]
  | some m, none   => /["midterm" := (85 ≤ m : Bool), "final" := EMP]
  | none, some f   => /["midterm" := EMP, "final" := (85 ≤ f : Bool)]
  | none, none   => /["midterm" := EMP, "final" := EMP]

#test
update [⟨("midterm", Bool), _⟩, ⟨("final", Bool), _⟩] gradebook didWellUpdate
=
Table.mk [
  /[ "Bob"   , 12  , 8     , 9     , false   , 7     , 9     , true  ],
  /[ "Alice" , 17  , 6     , 8     , true    , 8     , 7     , true  ],
  /[ "Eve"   , 13  , 7     , 9     , false   , 8     , 8     , false ]
]

-- `select`
#test
select students (λ (r : Row $ schema students) (n : {n // n < nrows students}) =>
  let colorCell : Cell "COLOR" String := Cell.fromOption $ getValue r "favorite color" (by header)
  let ageCell : Cell "AGE" Nat := Cell.fromOption $ getValue r "age" (by header)
  (Row.cons (Cell.val n.val : Cell "ID" Nat) $
  Row.cons colorCell $
  Row.cons ageCell
  Row.nil))
=
Table.mk [
  /[ 0  , "blue"  , 12  ],
  /[ 1  , "green" , 17  ],
  /[ 2  , "red"   , 13  ]
]

#test
select gradebook (λ (r : Row $ schema gradebook) (n : {n // n < nrows gradebook}) =>
  let nameCell : Cell "full name" String :=
    Cell.fromOption $ (getValue r "name" (by header)).map (· ++ " Smith")
  let mf2 : Cell "(midterm + final) / 2" Nat :=
    match getValue r "midterm" (by header), getValue r "final" (by header) with
    | some m, some f => Cell.val ((m + f) / 2)
    | _, _ => Cell.emp
  Row.cons nameCell $ Row.cons mf2 Row.nil
)
=
Table.mk [
  /[ "Bob Smith"   , 82                    ],
  /[ "Alice Smith" , 86                    ],
  /[ "Eve Smith"   , 80                    ]
]

-- `selectMany`
-- TODO: type class resolution fails if we annotate `r : Row $ schema students`
#test
selectMany students
(λ r n =>
  if n.val % 2 == 0
  then Table.mk [r]
  else head (Table.mk [r]) ⟨0, by simp [Int.abs, nrows]⟩)
(λ r₁ r₂ => r₂)
=
Table.mk [
  /[ "Bob" , 12  , "blue"         ],
  /[ "Eve" , 13  , "red"          ]
]

def repeatRow {sch : @Schema String} : Row sch → Nat → Table sch
| r, 0 => Table.mk [r]
| r, n+1 => addRows (repeatRow r n) [r]

def decertify {sch : @Schema String}
              (f : Row sch → Nat → Table sch)
              (r : Row sch)
              (nhn : {n // n < nrows gradebook}) :=
f r nhn.1

#test
selectMany gradebook (decertify repeatRow)
(λ r₁ r₂ =>
  Row.cons (Cell.fromOption (nm := "midterm") $
              getValue r₂ "midterm" (by header))
  Row.nil)
=
Table.mk [
  /[ 77      ],
  /[ 88      ],
  /[ 88      ],
  /[ 84      ],
  /[ 84      ],
  /[ 84      ]
]

-- `groupJoin`
def getName :=
λ {schema} (h : schema.HasCol ("name", String)) (r : Row schema) =>
  getValue r "name" h

def averageFinal := λ (r : Row $ schema students) (t : Table $ schema gradebook) =>
  r.addColumn "final"
              (some $ average $ List.filterMap id (getColumn2 t "final" (by header)))

#test
groupJoin students gradebook (getName (by header)) (getName (by header)) averageFinal
=[by inst]
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 87    ],
  /[ "Alice" , 17  , "green"        , 85    ],
  /[ "Eve"   , 13  , "red"          , 77    ]
]

def nameLength' :=
λ {schema} (h : schema.HasCol ("name", String)) (r : Row schema) =>
  (getValue r "name" h).map String.length

def tableNRows := λ (r : Row $ schema students) (t : Table $ schema gradebook) =>
  Row.addColumn r "nrows" (some $ nrows t)

#test
groupJoin students gradebook (nameLength' (by header)) (nameLength' (by header)) tableNRows
=[by inst]
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 2     ],
  /[ "Alice" , 17  , "green"        , 1     ],
  /[ "Eve"   , 13  , "red"          , 2     ]
]

-- `join`
def getName' :=
λ {schema} (h : schema.HasCol ("name", String)) (r : Row schema) =>
  getValue r "name" h

def addGradeColumn := λ (r₁ : Row $ schema students) (r₂ : Row $ schema gradebook) =>
  Row.addColumn r₁ "grade" (getValue r₂ "final" (by header))

#test
join students gradebook (getName' (by header)) (getName' (by header)) addGradeColumn
=[by inst]
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 87    ],
  /[ "Alice" , 17  , "green"        , 85    ],
  /[ "Eve"   , 13  , "red"          , 77    ]
]

def nameLength'' :=
λ {schema} (h : schema.HasCol ("name", String)) (r : Row schema) =>
  (getValue r "name" h).map String.length

#test
join students gradebook (nameLength'' $ by header) (nameLength'' $ by header) addGradeColumn
=[by inst]
Table.mk [
  /[ "Bob"   , 12  , "blue"         , 87    ],
  /[ "Bob"   , 12  , "blue"         , 77    ],
  /[ "Alice" , 17  , "green"        , 85    ],
  /[ "Eve"   , 13  , "red"          , 87    ],
  /[ "Eve"   , 13  , "red"          , 77    ]
]
