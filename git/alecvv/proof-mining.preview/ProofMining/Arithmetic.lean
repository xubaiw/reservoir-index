import ProofMining.Term
import ProofMining.Formula
import ProofMining.Lambda

def addition (x: Term) (y: Term): Term :=
  Term.recursorOne (0) # x # (Lambda.lambda [] 𝕆 ( Lambda.lambda [𝕆] 𝕆 (Term.successor # (Term.var 1)) 𝕆 ) (𝕆 ↣ 𝕆) ) # y

def multiplication (x: Term) (y: Term): Term :=
  Term.recursorOne (0) # 0 # (Lambda.lambda [] 𝕆 ( Lambda.lambda [𝕆] 𝕆 (addition x (Term.var 1)) 𝕆 ) (𝕆 ↣ 𝕆) ) # y

def proj : Term := Lambda.lambda [𝕆] 𝕆 (Lambda.lambda [𝕆, 𝕆] 𝕆 0 𝕆) _
def predecessor : Term :=
  Lambda.lambda [] 𝕆 (Term.recursorOne 0 # Term.zero # proj # (Term.var 0) ) _

def substraction (x: Term) (y: Term): Term :=
  Term.recursorOne (0) # x # (Lambda.lambda [] 𝕆 ( Lambda.lambda [𝕆] 𝕆 (predecessor # (Term.var 1)) 𝕆 ) (𝕆 ↣ 𝕆) ) # y

def sg : Term :=
  Lambda.lambda [] 𝕆 (Term.recursorOne 1 # Term.zero # ( Lambda.lambda [𝕆] 𝕆 ((Term.var 0)) 𝕆 ) ) _

def substractionMod (x: Term) (y: Term): Term :=
  addition (substraction x y) (substraction y x)

def arleq (x: Term) (y: Term): Formula :=
  (substraction x - y) ≅ 0

def arless (x: Term) (y: Term): Formula :=
  (arleq x y) ⋀ (∼ (x ≅ y))