import InfinityCategory.CategoryTheory.Category.NatTrans

section FuncCategory

def NatTrans_id_comp : ∀ {C : Category} {D : Category} {F G : Func C D} (α : NatTrans F G),
    NatTrans_comp (NatTrans_id F) α = α := by {
        intro C D F G α;
        have : ∀ (X : C), D.comp ((NatTrans_id F).to_func X) (α.to_func X) = (α.to_func X) := by {
            intro X;
            sorry;
        };
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
