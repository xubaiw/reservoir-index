import CategoryTheory.Basics
import CategoryTheory.Constructions

namespace CategoryTheory

def cov_yoneda {C : Category} (F : Functor C Typ) (A : C.ob) : Iso (NaturalTransformation (Hom_ A) F) (F.Θ A) := sorry

end CategoryTheory
