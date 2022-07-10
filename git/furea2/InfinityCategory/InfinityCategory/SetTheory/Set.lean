class Set where
    α   : Type u
    p   : α → Prop
instance : CoeSort Set (Type u) where
  coe A := A.α

section Set

def SetIn (A : Set) (a : A) : Prop := A.p a

def SetOfType (A : Set) := A.α
def SetOfProperty (A : Set) := A.p

def TypeToSet (A : Type u) : Set where
    α   := A
    p _ := True

class SetMap (A : Set) (B : Set) where
    map : A.α → B.α
    p   : ∀ (a : A.α), A.p a → B.p (map a)
def SetMapId (A : Set) : SetMap A A where
    map := fun a => a
    p   := fun _  h => h
def SetMapComp (g : SetMap B C) (f : SetMap A B) : SetMap A C where
    map := g.map ∘ f.map
    p   := fun a h => (g.p (f.map a)) ((f.p a) h)
class SetEq (A : Set) (B : Set) where
    to_map  : SetMap A B
    inv_map : SetMap B A
    to_inv  : (SetMapComp to_map inv_map).map = fun x => x
    inv_to  : (SetMapComp inv_map to_map).map = fun x => x
def ImageSet (f : SetMap A B) : Set where
    α   := B.α
    p   := fun b => ∃(a : A.α), b = f.map a


def SetSubset {α : Type u} {pA pB : α → Prop} (_ : (Set.mk α pA)) (_ : (Set.mk α pB)) :=
    ∀ (a : α), (pA a) → (pB a)
notation:50 " ⊂ " => SetSubset


end Set
