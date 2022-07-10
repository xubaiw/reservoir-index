import InfinityCategory.CategoryTheory.Category.Category
import InfinityCategory.CategoryTheory.Category.Opposite

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
