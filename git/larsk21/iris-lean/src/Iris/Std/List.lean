namespace List

@[reducible]
def isEmptyR : List α → Bool
  | []     => true
  | _ :: _ => false

@[reducible]
def eraseIdxR : (as : List α) → Fin as.length → List α
  | _ :: as, ⟨0, _⟩     => as
  | a :: as, ⟨i + 1, h⟩ => a :: eraseIdxR as ⟨i, Nat.le_of_succ_le_succ h⟩

@[specialize]
def foldl1 {α} (f : α → α → α) (alt : Unit → α) : List α → α
  | []     => alt ()
  | a :: l => l.foldl f a

@[specialize]
def foldr1 {α} (f : α → α → α) (alt : Unit → α) : List α → α
  | []     => alt ()
  | [a]    => a
  | a :: l => f a (foldr1 f alt l)

@[reducible]
def getR : (as : List α) → Fin as.length → α
  | a :: _ , ⟨0, _⟩     => a
  | a :: as, ⟨i + 1, h⟩ => getR as ⟨i, Nat.le_of_succ_le_succ h⟩

def splitWithSortedIndices (as : List α) (is : List Nat) : List α × List α :=
  go as is 0
where
  go (as : List α) (is : List Nat) (idx : Nat) : List α × List α :=
    match as with
    | a :: as =>
      match is with
      | i :: is =>
        if i == idx then
          go as is (idx + 1) |>.map (a :: ·) (·)
        else
          go as (i :: is) (idx + 1) |>.map (·) (a :: ·)
      | [] => ([], a :: as)
    | [] => ([], [])

end List
