import InfinityCategory.CategoryTheory.Category.Category

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
