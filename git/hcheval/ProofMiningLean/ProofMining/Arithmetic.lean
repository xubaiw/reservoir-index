import ProofMining.Term
import ProofMining.Lambda

def addition (x: Term) (y: Term): Term :=
  Term.recursorOne (0) # x # (Lambda.lambda [] 𝕆 ( Lambda.lambda [𝕆] 𝕆 (Term.successor # (Term.var 1)) 𝕆 ) (𝕆 ↣ 𝕆) ) # y

def proj : Term := Lambda.lambda [𝕆] 𝕆 (Lambda.lambda [𝕆, 𝕆] 𝕆 0 𝕆) _
def predecessor : Term :=
  Lambda.lambda [] 𝕆 (Term.recursorOne 0 # Term.zero # proj # (Term.var 0) ) _

def substraction (x: Term) (y: Term): Term :=
  Term.recursorOne (0) # x # (Lambda.lambda [] 𝕆 ( Lambda.lambda [𝕆] 𝕆 (predecessor # (Term.var 1)) 𝕆 ) (𝕆 ↣ 𝕆) ) # y