/-
This is a collection from a scala source
      "Every natural number is greater than $0$", 
      "Every natural number $n$, where $n$ is greater than $1$, is divisible by a prime number", 
      "Every natural number $n$ which is greater than $1$ is divisible by a prime number", 
      "if a prime number $p$ divides the product of $m$ and $n$,  $p$ divides one of $m$ and $n$",
      "if a prime number $p$ divides the product of $m$ and $n$,  $p$ divides $m$ or $n$", 
      "if a prime number $p$ divides $mn$, $p$ divides $m$ or $n$", 
      "Every natural number which is greater than $1$ is divisible by a prime number",
      "Every natural number $n$, which is greater than $1$, is divisible by a prime number", 
       "Six is not the sum of two distinct primes",
      "$6$ is not the sum of two distinct prime numbers",  'primes' causes trouble
      "Every natural number is greater than $0$",
       "The image of $Z$ in $K$ is an integral domain, hence isomorphic to $Z$ or $Z/p$, where $p$ is a prime",
      "If $G/H$ is cyclic, then $G$ is abelian", 
      "If $G/H$ is cyclic, $G$ is abelian", 
      "$\ker \phi$ is the set of all $a\in A$ that map to an element in $B$",
      "$6$ is not the square of a prime", 
      "$6$ is not the square of all prime numbers", ,
      "$6$ is not the sum of distinct prime numbers",
      "$6$ is not the square of all primes",
       "An abelian group is finitely generated if and only if the corresponding $Z$-module is finitely generated",
      "$G$ is solvable if there exists $n in \N$ such that $G^{(n)}=1$", 
      "there are $n,m\in \Z$ such that $xH = (gH)^n = g^nH$",
       "Two quadratic forms over $k$ are equivalent if and only if they have the same rank",
      "Two quadratic forms over $k$ are equivalent if and only if they have the same rank", experiment iff -> and
      "Two quadratic forms over $k$ are equivalent if and only if they have the same rank, same discriminant and same invariant $\epsilon$",
      "The discriminant of $g$ is equal to $d/a$", 
       "The number of elements of $k/k^2$ which are represented by $f$ is equal to $1$",
       "The number of elements of $k/k^2$ which are represented by $f$ is equal to $1$ if $n=1$, to $2^r -1$ if $n=3$, and to $2^r$ if $n=4$",
      "if $p$ is a prime number, the form deduced from $f$ by reduction modulo $p$ has a non-trivial root",
      "if $p$ is a prime number, the form deduced from $f$ by reduction modulo $p$ has a non-trivial zero, and this zero can be lifted to a p-adic zero",
      "the quadratic form $f$ represents zero in all the $Q_p$, and also in $R$",
      "if two diagrams $D_1$ and $D_2$ are related by a chain of Reidemeister moves, the complexes of graded abelian groups $C(D_1)$ and $C(D_2)$ are equivalent and homology groups $H(D_1)$ and $H(D_2)$ are isomorphic",
      "$AB \subgroup G$ if and only if $AB = BA$", 
      "$AB \subgroup G$ and $AB = BA$", experiment iff -> and; 
      "$[A,B] = \{e\}$ if and only if $ab = ba, \forall a \in A, b \in B$ if and only if $A \subgroup C_G(B)$ if and only if $B \subgroup C_G(A)$"
-/
open Nat 

def Nat.divides (a b : Nat) : Prop := b % a = 0

infix:65 "|" => Nat.divides

def prime(n: Nat): Prop := (n > 1) ∧ (∀ d: Nat, d | n → d = 1 ∨ d = n)

/- Text: Every natural number is greater than $0$  -/
example : Prop := ∀ n : Nat, n > 0

/- 
* Text: Every natural number $n$, where $n$ is greater than $1$, is divisible by a prime number 

* Text: Every natural number $n$ which is greater than $1$ is divisible by a prime number
-/
example : Prop := ∀ n : Nat, n > 1 → ∃ p : Nat, prime p ∧  p | n

/-
Text: if a prime number $p$ divides the product of $m$ and $n$,  $p$ divides one of $m$ and $n$

Text: if a prime number $p$ divides the product of $m$ and $n$,  $p$ divides $m$ or $n$"

Text: if a prime number $p$ divides $mn$, $p$ divides $m$ or $n$
-/
example : Prop := ∀ p : Nat, prime p → ∀ m n : Nat, p | m * n → p | m ∨ p | n

/-
* Text: Six is not the sum of two distinct primes
* Text: $6$ is not the sum of two distinct prime numbers
-/
example : Prop := ¬ (∃ n m: Nat, prime n ∧ prime m ∧ n ≠ m ∧ 6 = n + m)
