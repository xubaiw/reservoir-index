import GMLAlgebra.Signatures
import GMLAlgebra.Identities
import GMLAlgebra.UnitalRig
import GMLAlgebra.UnitalRing
import GMLAlgebra.UnitalSemiring

namespace Algebra
variable (α)
  [HAdd α α α] [Neg α] [OfNat α (nat_lit 0)]
  [HMul α α α] [Inv α] [OfNat α (nat_lit 1)]

def addSemigroupSig : SemigroupSig α where
  op := (.+.)

unif_hint (t : SemigroupSig α) where
  t =?= addSemigroupSig α ⊢ t.op =?= (.+.)

def addMonoidSig : MonoidSig α where
  toSemigroupSig := addSemigroupSig α
  id := 0

unif_hint (t : MonoidSig α) where
  t =?= addMonoidSig α ⊢ t.toSemigroupSig =?= addSemigroupSig α

unif_hint (t : MonoidSig α) where
  t =?= addMonoidSig α ⊢ t.id =?= 0

def addGroupSig : GroupSig α where
  toMonoidSig := addMonoidSig α
  inv := (-.)

unif_hint (t : GroupSig α) where
  t =?= addGroupSig α ⊢ t.toMonoidSig =?= addMonoidSig α

unif_hint (t : GroupSig α) where
  t =?= addGroupSig α ⊢ t.inv =?= (-.)

def mulSemigroupSig : SemigroupSig α where
  op := (.*.)

unif_hint (t : SemigroupSig α) where
  t =?= mulSemigroupSig α ⊢ t.op =?= (.*.)

def mulMonoidSig : MonoidSig α where
  toSemigroupSig := mulSemigroupSig α
  id := 1

unif_hint (t : MonoidSig α) where
  t =?= mulMonoidSig α ⊢ t.toSemigroupSig =?= mulSemigroupSig α

unif_hint (t : MonoidSig α) where
  t =?= mulMonoidSig α ⊢ t.id =?= 1

def mulGroupSig : GroupSig α where
  toMonoidSig := mulMonoidSig α
  inv := (.⁻¹)

unif_hint (t : GroupSig α) where
  t =?= mulGroupSig α ⊢ t.toMonoidSig =?= mulMonoidSig α

unif_hint (t : GroupSig α) where
  t =?= mulGroupSig α ⊢ t.inv =?= (.⁻¹)

def addMulSemiringSig : SemiringSig α where
  add := (.+.)
  mul := (.*.)

unif_hint (t : SemiringSig α) where
  t =?= addMulSemiringSig α ⊢ t.toAddSemigroupSig =?= addSemigroupSig α

unif_hint (t : SemiringSig α) where
  t =?= addMulSemiringSig α ⊢ t.toMulSemigroupSig =?= mulSemigroupSig α

unif_hint (t : SemiringSig α) where
  t =?= addMulSemiringSig α ⊢ t.add =?= (.+.)

unif_hint (t : SemiringSig α) where
  t =?= addMulSemiringSig α ⊢ t.mul =?= (.*.)

def addMulRigSig : RigSig α where
  toSemiringSig := addMulSemiringSig α
  zero := 0

unif_hint (t : RigSig α) where
  t =?= addMulRigSig α ⊢ t.toAddMonoidSig =?= addMonoidSig α

unif_hint (t : RigSig α) where
  t =?= addMulRigSig α ⊢ t.toSemiringSig =?= addMulSemiringSig α

unif_hint (t : RigSig α) where
  t =?= addMulRigSig α ⊢ t.zero =?= 0

def addMulRingSig : RingSig α where
  toRigSig := addMulRigSig α
  neg := (-.)

unif_hint (t : RingSig α) where
  t =?= addMulRingSig α ⊢ t.toAddGroupSig =?= addGroupSig α

unif_hint (t : RingSig α) where
  t =?= addMulRingSig α ⊢ t.toRigSig =?= addMulRigSig α

unif_hint (t : RingSig α) where
  t =?= addMulRingSig α ⊢ t.neg =?= (-.)

def addMulUnitalSemiringSig : UnitalSemiringSig α where
  toSemiringSig := addMulSemiringSig α
  one := 1

unif_hint (t : UnitalSemiringSig α) where
  t =?= addMulUnitalSemiringSig α ⊢ t.toMulMonoidSig =?= mulMonoidSig α

unif_hint (t : UnitalSemiringSig α) where
  t =?= addMulUnitalSemiringSig α ⊢ t.toSemiringSig =?= addMulSemiringSig α

unif_hint (t : UnitalSemiringSig α) where
  t =?= addMulUnitalSemiringSig α ⊢ t.one =?= 1

def addMulUnitalRigSig : UnitalRigSig α where
  toRigSig := addMulRigSig α
  one := 1

unif_hint (t : UnitalRigSig α) where
  t =?= addMulUnitalRigSig α ⊢ t.toUnitalSemiringSig.toMulMonoidSig =?= mulMonoidSig α

unif_hint (t : UnitalRigSig α) where
  t =?= addMulUnitalRigSig α ⊢ t.toUnitalSemiringSig =?= addMulUnitalSemiringSig α

unif_hint (t : UnitalRigSig α) where
  t =?= addMulUnitalRigSig α ⊢ t.toSemiringSig =?= addMulSemiringSig α

unif_hint (t : UnitalRigSig α) where
  t =?= addMulUnitalRigSig α ⊢ t.one =?= 1

def addMulUnitalRingSig : UnitalRingSig α where
  toRingSig := addMulRingSig α
  one := 1

unif_hint (t : UnitalRingSig α) where
  t =?= addMulUnitalRingSig α ⊢ t.toMulMonoidSig =?= mulMonoidSig α

unif_hint (t : UnitalRingSig α) where
  t =?= addMulUnitalRingSig α ⊢ t.toUnitalSemiringSig =?= addMulUnitalSemiringSig α

unif_hint (t : UnitalRingSig α) where
  t =?= addMulUnitalRingSig α ⊢ t.toUnitalRigSig =?= addMulUnitalRigSig α

unif_hint (t : UnitalRingSig α) where
  t =?= addMulUnitalRingSig α ⊢ t.toSemiringSig =?= addMulSemiringSig α

unif_hint (t : UnitalRingSig α) where
  t =?= addMulUnitalRingSig α ⊢ t.one =?= 1

end Algebra

section instances
open Algebra

instance Pos.instUnitalCommSemiring : UnitalCommSemiring (addMulUnitalSemiringSig Pos) where
  add_assoc := Pos.add_assoc
  add_comm := Pos.add_comm
  mul_assoc := Pos.mul_assoc
  mul_comm := Pos.mul_comm
  mul_right_id := Pos.mul_one
  mul_right_distrib := Pos.right_distrib

instance Nat.instUnitalCommRig : UnitalCommRig (addMulUnitalRigSig Nat) where
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  add_right_id := Nat.add_zero
  mul_assoc := Nat.mul_assoc
  mul_comm := Nat.mul_comm
  mul_right_id := Nat.mul_one
  mul_right_distrib := Nat.right_distrib
  mul_right_zero := Nat.mul_zero

instance Int.instUnitalCommRing : UnitalCommRing (addMulUnitalRingSig Int) where
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  add_right_id := Int.add_zero
  add_right_inv := Int.add_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  mul_right_id := Int.mul_one
  mul_right_distrib := Int.add_mul

end instances
