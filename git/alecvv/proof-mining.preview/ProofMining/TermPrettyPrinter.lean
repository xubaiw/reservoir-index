import ProofMining.Term 
import ProofMining.Options
import Lean 
import ProofMining.FiniteTypePrettyPrinter

open Lean PrettyPrinter Delaborator SubExpr 
open Term


@[delab app.Term.kcomb]
def delabK : Delab := do 
  let printTypes ← getBoolOption print_types.name 
  let e ← getExpr 
  guard $ e.getAppNumArgs == 2 
  let ρ ← withAppFn $ withAppArg Delaborator.delab 
  let τ ← withAppArg Delaborator.delab
  if printTypes  
    then `(K $ρ $τ) 
    else `(K)

@[delab app.Term.scomb] 
def delabS : Delab := do 
  let printTypes ← getBoolOption print_types.name 
  let e ← getExpr 
  guard $ e.getAppNumArgs == 3 
  let ρ ← withAppFn $ withAppFn $ withAppArg Delaborator.delab 
  let τ ← withAppFn $ withAppArg Delaborator.delab 
  let σ ← withAppArg Delaborator.delab 
  if printTypes 
    then `(S $ρ $τ $σ) 
    else `(S)

