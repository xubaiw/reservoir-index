class Dvd (α : Type u) :=
(dvd : α → α → Bool)

notation:50 a:50 " ∣ " b:51 => Dvd.dvd a b
