> There should be one-- and preferably only one --obvious way to do it.
> Although that way may not be obvious at first unless you're Dutch.

- PEP 20 - The Zen of Python

```lean
-- How many different ways can we write an inductive type for the naturals?
inductive Nat1 where
  | zero : Nat1
  | succ (n : Nat1) : Nat1
deriving Repr

inductive Nat2 where
  | zero : Nat2
  | succ : Nat2 → Nat2
deriving Repr

inductive Nat3 where
  | zero
  | succ (n : Nat3)
deriving Repr

inductive Nat4
  | zero
  | succ (n : Nat4)
deriving Repr

inductive Nat5
| zero
| succ (n : Nat5)
deriving Repr

#eval Nat1.succ Nat1.zero
#eval Nat2.succ Nat2.zero
#eval Nat3.succ Nat3.zero
#eval Nat4.succ Nat4.zero
#eval Nat5.succ Nat5.zero
```
