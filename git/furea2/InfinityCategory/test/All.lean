-- noncomputable

section Category
class Quiver where
    ob  : Type u
    hom : ob → ob → Type v

class PreCategory extends Quiver where
    id    : (X : ob) → (hom X X)
    comp  : (hom X Y) → (hom Y Z) → (hom X Z)

infixr:80 " ○ " => PreCategory.comp

class Category extends PreCategory where
    id_comp : (f : hom X Y) → ((id X) ○ f) = f
    comp_id : (f : hom X Y) → (f ○ (id Y)) = f
    assoc   : ∀ {X Y Z W : ob} (f : hom W X) (g : hom X Y) (h : hom Y Z),
                (f ○ g) ○ h = f ○ (g ○ h)
instance : CoeSort Category (Type u) where
    coe c := c.ob

class CategoryObjIso {C : Category} (X Y : C) where
    hom : C.hom X Y
    inv : C.hom Y X
    hom_inv_id  : hom ○ inv = C.id X
    inv_hom_id  : inv ○ hom = C.id Y
instance {C : Category} {X Y : C.ob} : CoeSort (CategoryObjIso X Y) (C.hom X Y) where
    coe c := c.hom
def HomIsObjIso {C : Category} {X Y : C} (f : C.hom X Y) :=
    ∃ (h : CategoryObjIso X Y), h.hom = f

infix:80 " =ob= " => CategoryObjIso

end Category

section Func
class PreFunc (C : Quiver) (D : Quiver) :=
    ob_map  : C.ob → D.ob
    hom_map : ∀{X Y : C.ob},(C.hom X Y) → (D.hom (ob_map X) (ob_map Y))
class Func (C : Category) (D : Category)
    extends PreFunc (C.toQuiver : Quiver) (D.toQuiver : Quiver) where
    map_id      : ∀ (X : C), hom_map (C.id X) = D.id (ob_map X)
    map_comp    : ∀ {X Y Z : C} (f : C.hom X Y) (g : C.hom Y Z),
                    hom_map (C.comp f g) = D.comp (hom_map f) (hom_map g)
instance : CoeSort (Func C D) (C.ob → D.ob) where
    coe X := X.ob_map
def Func_id (C : Category) : Func C C where
    ob_map      := fun X => X
    hom_map     := fun f => f
    map_id      := fun _ => rfl
    map_comp    := fun _ _ => rfl

def Func_comp {C : Category} {D : Category} {E : Category} (F : Func C D) (G : Func D E) : Func C E where
    ob_map      := G.ob_map ∘ F.ob_map
    hom_map     := G.hom_map ∘ F.hom_map;
    map_id      := by {
        intro X;
        have : (G.hom_map ∘ F.hom_map) (C.id X) = E.id ((G.ob_map ∘ F.ob_map) X) := by {
            have : E.id (G.ob_map (F.ob_map X)) = E.id (Function.comp G.ob_map F.ob_map X) := rfl;
            rw [Function.comp, F.map_id, G.map_id, this];
        };
        exact this;
    }
    map_comp    := by {
        intro X Y Z f g;
        have : (G.hom_map ∘ F.hom_map) (C.comp f g) = E.comp ((G.hom_map ∘ F.hom_map) f) ((G.hom_map ∘ F.hom_map) g) := by {
            rw [Function.comp, F.map_comp, G.map_comp, Function.comp, Function.comp];
        };
        exact this;
    }

class CategoryIso (C : Category) (D : Category) where
    to_func     : Func C D
    inv_func    : Func D C
    to_inv_id   : (Func_comp F G) = Func_id C
    inv_to_id   : (Func_comp G F) = Func_id D

end Func

section NatTrans

class NatTrans {C : Category} {D : Category} (F G : Func C D) where
    to_func : ∀ (X : C), D.hom (F.ob_map X) (G.ob_map X)
    comm    : ∀ (X Y : C.ob) (f : C.hom X Y),
                    D.comp (to_func X) (G.hom_map f) = D.comp (F.hom_map f) (to_func Y)

def NatTrans_id {C : Category} {D : Category} (F : Func C D) : NatTrans F F where
    to_func := fun X => D.id (F.ob_map X);
    comm    := by {
        intro X Y f;
        have h1 :
                D.comp ((fun X => D.id (F.ob_map X)) X) (F.hom_map f)
            =   D.comp (D.id (F.ob_map X)) (F.hom_map f) := by rfl;
        have h2 :
                D.comp (F.hom_map f) ((fun X => D.id (F.ob_map X)) Y)
            =   D.comp (F.hom_map f) (D.id (F.ob_map Y)) := by rfl;
        have h3 : D.comp (D.id (F.ob_map X)) (F.hom_map f) = (F.hom_map f) := D.id_comp (F.hom_map f);
        have h4 : (F.hom_map f) = D.comp (F.hom_map f) (D.id (F.ob_map Y)) := (D.comp_id (F.hom_map f)).symm;
        rw [h1, h2, h3];
        exact h4;
    }

def NatTrans_comp {C : Category} {D : Category} {F G H : Func C D}
        (α : NatTrans F G) (β : NatTrans G H)  : NatTrans F H where
    to_func := fun X => D.comp (α.to_func X) (β.to_func X)
    comm    := by {
        intro X Y f;
        have h1 (Z : C) :
                ((fun X => D.comp (α.to_func X) (β.to_func X)) Z)
            =   (D.comp (α.to_func Z) (β.to_func Z)) := by rfl;
        rw [h1,
            h1,
            D.assoc,
            β.comm,
            (D.assoc _ _ _).symm,
            α.comm,
            D.assoc];
    }


end NatTrans

section FuncCategory

def NatTrans_id_comp : ∀ {C : Category} {D : Category} {F G : Func C D} (α : NatTrans F G),
    NatTrans_comp (NatTrans_id F) α = α := by {
        intro C D F G α;
        have : ∀ (X : C), D.comp ((NatTrans_id F).to_func X) (α.to_func X) = (α.to_func X) := by {
            intro X;
            sorry;
        };
        -- exact ⟨this, True⟩;
        -- have := (fun X => NatTrans.to_func X) ○ G.to_func X;
        sorry;
    }
def NatTrans_comp_id : ∀ {C : Category} {D : Category} {F G : Func C D} (α : NatTrans F G),
    NatTrans_comp α (NatTrans_id G) = α := by {intro C D F G α; sorry;}
def NatTrans_assoc : ∀ {C : Category} {D : Category} {F G H I : Func C D}
    (α : NatTrans F G) (β : NatTrans G H) (γ : NatTrans H I),
    NatTrans_comp (NatTrans_comp α β) γ = NatTrans_comp α (NatTrans_comp β γ) := by sorry

def FuncCategory (C : Category) (D : Category) : Category where
    ob      := Func C D
    hom     := NatTrans
    id      := NatTrans_id
    comp    := NatTrans_comp
    id_comp := NatTrans_id_comp
    comp_id := NatTrans_comp_id
    assoc   := NatTrans_assoc

end FuncCategory

section Opposite
def opposite (C : Category) : Category where
    ob      := C.ob
    hom     := fun A B => C.hom B A
    id      := C.id
    comp    := fun f g => C.comp g f
    id_comp := C.comp_id
    comp_id := C.id_comp
    assoc   := fun f g h => (C.assoc h g f).symm

notation C "ᵒᵖ" => opposite C
end Opposite

section SimplexCategory
def monotone (f : α → β) [LE α] [LE β] : Prop := ∀ a b : α, a ≤ b → f a ≤ f b

def simplex_hom (n m : Nat) := {f : Fin n → Fin m // monotone f}

theorem id_is_monotone : monotone (fun (x : Fin n) => x) :=
    fun _ _ h => h
theorem comp_is_monotone {n m k : Nat} (f : simplex_hom n m) (g : simplex_hom m k) : monotone (g.val ∘ f.val) :=
    fun a b h => g.property (f.val a) (f.val b) (f.property a b h)


def SimplexCategory : Category where
    ob      := Nat
    hom {n m : Nat} := simplex_hom n m
    id      := fun _ => ⟨fun x => x, id_is_monotone⟩
    comp    := by {
        intro X Y Z f g;
        exact ⟨g.val ∘ f.val, comp_is_monotone f g⟩;
    }
    id_comp := by {intro _ _ _; rfl;}
    comp_id := by {intro _ _ _; rfl;}
    assoc   := by {intro _ _ _ _ _ _ _; rfl;}
instance : OfNat SimplexCategory n where
    ofNat := n

def SimplexCategoryOp : Category := SimplexCategoryᵒᵖ
instance : OfNat SimplexCategoryOp n where
    ofNat := n

end SimplexCategory

section SimplicialObject
def SimplicialObject (C : Category) :=
    Func (SimplexCategoryᵒᵖ) C
end SimplicialObject

section SetCategory

def SetCategory.{u} : Category where
    ob      := Type u
    hom     := fun (A B : Type u) => (A → B)
    id      := fun (A : Type u) => (fun (x : A) => x)
    comp    := fun {A B C : Type u} (f : A → B) (g : B → C) => g ∘ f
    id_comp := fun _ => rfl
    comp_id := fun _ => rfl
    assoc   := fun _ _ _ => rfl
end SetCategory

section SimplicialSet
def yoneda (C : Category) : Category :=
    FuncCategory C (FuncCategory (Cᵒᵖ) SetCategory)
def SSet.{u} := FuncCategory (SimplexCategoryᵒᵖ) SetCategory.{u}
def StandardSimplexCategory := yoneda SSet

def StandardSimplex (n : Nat) : SSet where
    ob_map      := fun m => (simplex_hom m n)
    hom_map     := by {
        intro m k f;
        exact fun σ => ⟨σ.val ∘ f.val , comp_is_monotone f σ⟩;
    }
    map_id      := by {intro _; rfl;}
    map_comp    := by {intro _ _ _ _ _; rfl;}

instance : OfNat SSet n where
  ofNat := StandardSimplex n
local notation "Δ["n"]" => StandardSimplex n

end SimplicialSet

