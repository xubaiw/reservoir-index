/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.MeasureTheory.Function.ConditionalExpectation

/-! # Notations for probability theory

This file defines the following notations, for functions `X,Y`, measures `P, Q` defined on a
measurable space `m0`, and another measurable space structure `m` with `hm : m ≤ m0`,
- `P[X] = ∫ a, X a ∂P`
- `𝔼[X] = ∫ a, X a`
- `𝔼[X|m,hm]`: conditional expectation of `X` with respect to the measure `volume` and the
  measurable space `m`. The similar `P[X|m,hm]` for a measure `P` is defined in
  measure_theory.function.conditional_expectation.
- `X =ₐₛ Y`: `X =ᵐ[volume] Y`
- `X ≤ₐₛ Y`: `X ≤ᵐ[volume] Y`
- `∂P/∂Q = P.rn_deriv Q`
We note that the notation `∂P/∂Q` applies to three different cases, namely,
`measure_theory.measure.rn_deriv`, `measure_theory.signed_measure.rn_deriv` and
`measure_theory.complex_measure.rn_deriv`.

- `ℙ` is a notation for `volume` on a measured space.
-/


open MeasureTheory

-- mathport name: «expr𝔼[ | ]»
-- We define notations `𝔼[f|hm]` and `𝔼[f|m,hm]` for the conditional expectation of `f` with
-- respect to `m`. Both can be used in code but only the second one will be used by the goal view.
-- The first notation avoids the repetition of `m`, which is already present in `hm`. The second
-- one ensures that `m` stays visible in the goal view: when `hm` is complicated, it gets rendered
-- as `_` and the measurable space would not be visible in `𝔼[f|_]`, but is clear in `𝔼[f|m,_]`.
localized [ProbabilityTheory]
  notation "𝔼[" X "|" hm "]" => MeasureTheory.condexp _ hm MeasureTheory.MeasureSpace.volume X

-- mathport name: «expr𝔼[ | , ]»
localized [ProbabilityTheory]
  notation "𝔼[" X "|" m "," hm "]" => MeasureTheory.condexp m hm MeasureTheory.MeasureSpace.volume X

-- mathport name: «expr [ ]»
localized [ProbabilityTheory] notation P "[" X "]" => ∫ x, X x ∂P

-- mathport name: «expr𝔼[ ]»
localized [ProbabilityTheory] notation "𝔼[" X "]" => ∫ a, X a

-- mathport name: «expr =ₐₛ »
localized [ProbabilityTheory] notation:50 X "=ₐₛ" Y:50 => X =ᵐ[MeasureTheory.MeasureSpace.volume] Y

-- mathport name: «expr ≤ₐₛ »
localized [ProbabilityTheory] notation:50 X "≤ₐₛ" Y:50 => X ≤ᵐ[MeasureTheory.MeasureSpace.volume] Y

-- mathport name: «expr∂ /∂ »
localized [ProbabilityTheory] notation "∂" P "/∂" Q:50 => P.rnDeriv Q

-- mathport name: «exprℙ»
localized [ProbabilityTheory] notation "ℙ" => MeasureTheory.MeasureSpace.volume

