import InfinityCategory.CategoryTheory.Category.Functor

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
