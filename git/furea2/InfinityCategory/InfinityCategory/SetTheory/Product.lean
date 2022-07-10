import InfinityCategory.SetTheory.Set

-- class Pi {I : Sort u} (A : I → Sort v) :=
--     x : (i : I) → (A i)

def PiType {I : Set} (A : I.α → Set) :=
    { x : (i : I) → (A i) // ∀ (i : I), (I.p i) → (A i).p (x i) }
def SigmaType {I : Set} (A : I.α → Set) :=
    { x : Sigma (fun (i : I.α) => (A i).α) // (A x.fst).p x.snd }

def Cartesian {I : Set} {A : I.α → Set} : Set := TypeToSet (PiType A)
def Cocartesian {I : Set} {A : I.α → Set} : Set := TypeToSet (SigmaType A)

def ProdType (A B : Set) :=
    @PiType (TypeToSet (Fin 2)) (fun (i : Fin 2) =>
        match (i : Fin 2) with
            | 0 => A
            | 1 => B)
def CoprodType (A B : Set) :=
    @SigmaType (TypeToSet (Fin 2)) (fun (i : Fin 2) =>
        match (i : Fin 2) with
            | 0 => A
            | 1 => B)

def ProdSet (A B : Set) : Set := TypeToSet (ProdType A B)
def CoprodSet (A B : Set) : Set := TypeToSet (CoprodType A B)

