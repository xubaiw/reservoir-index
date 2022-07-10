import InfinityCategory.CategoryTheory.Category.Category

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
