inductive mynat where
  | zero : mynat
  | succ : mynat → mynat
  deriving Repr

namespace mynat

def myofnat (n : Nat) :=
  match n with
  | 0 => mynat.zero
  | Nat.succ n' => mynat.succ (myofnat n')

instance : OfNat mynat n where
  ofNat := myofnat n

def toNat (n : mynat) :=
  match n with
  | mynat.zero => 0
  | mynat.succ n' => Nat.succ (toNat n')

instance : Coe mynat Nat where
  coe := toNat

theorem mynat_zero_eq_zero : mynat.zero = 0 := rfl
theorem one_eq_succ_zero : 1 = mynat.succ 0 := rfl

end mynat

