import Iris.BI
import Iris.Proofmode.Classes
import Iris.Proofmode.Environments
import Iris.Std.List
import Iris.Std.TC

namespace Iris.Proofmode
open Iris.BI Iris.Std

-- proof mode
theorem tac_start [BI PROP] (P : PROP) :
  envs_entails ⟨[], []⟩ P →
  ⊢ P
:= sorry

-- implication and wand
theorem tac_impl_intro [BI PROP] {Γₚ Γₛ : List PROP} {P Q : PROP} (R : PROP) :
  [FromImpl R P Q] →
  [TCIte Γₛ.isEmptyR TCTrue (Persistent P)] →
  [FromAffinely P' P] →
  envs_entails ⟨Γₚ, Γₛ.concat P'⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_impl_intro_intuitionistic [BI PROP] {Γₚ Γₛ : List PROP} {P P' Q : PROP} (R : PROP) :
  [FromImpl R P Q] →
  [IntoPersistent false P P'] →
  envs_entails ⟨Γₚ.concat P', Γₛ⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_wand_intro [BI PROP] {Γₚ Γₛ : List PROP} {P Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  envs_entails ⟨Γₚ, Γₛ.concat P⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

theorem tac_wand_intro_intuitionistic [BI PROP] {Γₚ Γₛ : List PROP} {P P' Q : PROP} (R : PROP) :
  [FromWand R P Q] →
  [IntoPersistent false P P'] →
  [TCOr (Affine P) (Absorbing Q)] →
  envs_entails ⟨Γₚ.concat P', Γₛ⟩ Q →
  envs_entails ⟨Γₚ, Γₛ⟩ R
:= sorry

-- assumptions
theorem tac_assumption [BI PROP] {Γₚ Γₛ : List PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let (p, i, P) : Bool × Nat × PROP := match i with
    | .p i => (true, i, Γₚ.getR i)
    | .s i => (false, i, Γₛ.getR i)
  [FromAssumption p P Q] →
  let Γₛ' := Γₛ.eraseIdxR i
  [TCIte Γₛ'.isEmptyR TCTrue (TCOr (Absorbing Q) (AffineEnv Γₛ'))] →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

-- false
theorem tac_false_destruct [BI PROP] {Γₚ Γₛ : List PROP} (i : EnvsIndex Γₚ.length Γₛ.length) (Q : PROP) :
  let P := match i with
    | .p i => Γₚ.getR i
    | .s i => Γₛ.getR i
  P = `[iprop| False] →
  envs_entails ⟨Γₚ, Γₛ⟩ Q
:= sorry

end Iris.Proofmode
