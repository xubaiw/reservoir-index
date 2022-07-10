import InfinityCategory.CategoryTheory.FuncCategory
import InfinityCategory.CategoryTheory.SetCategory
import InfinityCategory.SimplicialSet.SimplexCategory


section SimplicialSet
def yoneda (C : Category) : Category :=
    FuncCategory C (FuncCategory (Cᵒᵖ) SetCategory)
def SSet.{u} := FuncCategory (SimplexCategoryᵒᵖ) SetCategory.{u}
def StandardSimplexCategory := yoneda SSet

def StandardSimplex (n : Nat) : SSet where
    ob_map      := fun m => (simplex_hom m n)
    hom_map     := by {
        intro m k f;
        exact fun σ => ⟨σ.val ∘ f.val , comp_is_monotone f σ⟩;}
    map_id      := by {intro _; rfl;}
    map_comp    := by {intro _ _ _ _ _; rfl;}

instance : OfNat SSet n where
  ofNat := StandardSimplex n
local notation "Δ["n"]" => StandardSimplex n

end SimplicialSet

