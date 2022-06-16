import ProofMining.FiniteType 
import ProofMining.Options
import Lean 

open Lean PrettyPrinter Delaborator SubExpr 

namespace FiniteType 

@[appUnexpander FiniteType.zero]
def unexpandZero : Unexpander 
| `(zero) => `(𝕆)
| _ => throw ()
