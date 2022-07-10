import InfinityCategory.CategoryTheory.Category.Category

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
