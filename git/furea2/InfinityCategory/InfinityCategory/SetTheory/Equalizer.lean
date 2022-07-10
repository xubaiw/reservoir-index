import InfinityCategory.SetTheory.Set
import InfinityCategory.SetTheory.Product


-- Equalizer
def Equalizer {A B : Set} (f g : SetMap A B) : Set where
    α   := A.α
    p   := fun (a : A.α) => (A.p a) → (f.map a) = (g.map a)

-- Pullback
def ProdSetProj_0 (A B : Set) : SetMap (ProdSet A B) A where
    map :=  fun r => r.1 (0 : Fin 2)
    p   :=  sorry

def ProdSetProj_1 (A B : Set) : SetMap (ProdSet A B) B where
    map :=  fun r => r.1 (1 : Fin 2)
    p   :=  sorry
def Pullback {A B C : Set} (f : SetMap A C) (g : SetMap B C) : Set :=
    @Equalizer (ProdSet A B) C (SetMapComp f (ProdSetProj_0 A B)) (SetMapComp g (ProdSetProj_1 A B))


-- RelationSet
def RelationSetRelation {A : Set} (pR : (ProdType A A) → Prop) (a b : A) :=
    (a = b) ∨
    (∃(r : ProdType A A),
        (pR r) ∧ (r.1 (0 : Fin 2) = a) ∧ (r.1 (1 : Fin 2) = b))
def RelationSetIsEquivalenceSet {A : Set} (pR : (ProdType A A) → Prop) : Prop :=
    Equivalence (RelationSetRelation pR)

-- Coequalizer
def CoequalizerRelSet {A B : Set} (f g : SetMap A B) : Set where
    α := B.α
    p := fun b => ∃(a : A), ((f.map a) = b) ∨ ((g.map a) = b)
def CoequalizerRelation' {n : Nat} {A : Set} {B : Set} (rx : Fin n → A) (f g : SetMap A B) (a b : B) : Prop :=
  match n with
  | 0 => a = b
  | n+1 => ∀ (i : Fin (n+2)), match i with
    | ⟨0, _⟩   => a = f.map (rx ⟨0, Nat.succ_pos _⟩)
    | ⟨1, _⟩   => g.map (rx ⟨n, Nat.lt.base _⟩) = b
    | ⟨i+2, h⟩ =>
      g.map (rx ⟨i, (Nat.lt.step (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)))⟩)
      = f.map (rx ⟨i+1, (Nat.lt_of_succ_lt_succ h)⟩)
def CoequalizerRelation'_symm {n : Nat} {A : Set} {B : Set} (rx : Fin n → A) (f g : SetMap A B) (a b : B) :
    CoequalizerRelation' rx f g a b → CoequalizerRelation' rx g f b a  := sorry
def CoequalizerRelation {A : Set} {B : Set} (f g : SetMap A B) (a b : B) : Prop :=
    (a = b) ∨ ∃ (n:Nat) (rx : Fin n → A),
    (CoequalizerRelation' rx f g a b) ∨ (CoequalizerRelation' rx g f a b)
def CoequalizerRelation_refl {A : Set} {B : Set} (f g : SetMap A B) (a : B) :
    CoequalizerRelation f g a a := Or.inl rfl
def CoequalizerRelation_symm {A : Set} {B : Set} (f g : SetMap A B) {a b : B} :
    CoequalizerRelation f g a b → CoequalizerRelation f g b a := by {
        intro h;
        cases h;
        case inl h => {exact Or.inl h.symm;}
        case inr h => {
            have ⟨n, rx, hrx⟩ := h;
            apply Or.inr;
            exists n, rx;
            cases hrx;
            case h.inl hrx => {exact Or.inr (CoequalizerRelation'_symm rx f g a b hrx);}
            case h.inr hrx => {exact Or.inl (CoequalizerRelation'_symm rx g f a b hrx);}
        }
    }
def CoequalizerRelation_trans {A : Set} {B : Set} (f g : SetMap A B) {a b c: B} :
    CoequalizerRelation f g a b → CoequalizerRelation f g b c
        → CoequalizerRelation f g a c := by {
        intro h1 h2;
        cases h1;
        case inl h1 => {rw [←h1] at h2; exact h2;}
        case inr h1 => {
            have ⟨n1, rx1, hrx1⟩ := h1;
            apply Or.inr;
            cases h2;
            case inl h2 => {rw [←h2]; exact h1;}
            case inr h2 => {
                have ⟨n2, rx2, hrx2⟩ := h2;
                exists n1+n2;
                sorry;
            }
        }
    }
def CoequalizerRelationIsEquivalent {A B : Set} (f g : SetMap A B) :
    Equivalence (CoequalizerRelation f g) := {
    refl := CoequalizerRelation_refl f g
    symm := CoequalizerRelation_symm f g
    trans := CoequalizerRelation_trans f g
}

def Coequalizer {A B : Set} (f g : SetMap A B) : Set :=
    TypeToSet (Quotient (Setoid.mk
        (CoequalizerRelation f g)
        (CoequalizerRelationIsEquivalent f g)))
