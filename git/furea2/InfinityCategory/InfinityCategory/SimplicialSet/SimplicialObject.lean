import InfinityCategory.CategoryTheory.Category.Category
import InfinityCategory.CategoryTheory.Category.Functor
import InfinityCategory.SimplicialSet.SimplexCategory


section SimplicialObject
def SimplicialObject (C : Category) :=
    Func (SimplexCategoryᵒᵖ) C
end SimplicialObject
