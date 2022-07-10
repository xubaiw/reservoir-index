
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
