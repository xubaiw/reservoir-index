/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.MeasureTheory.Function.ConditionalExpectation.Real

/-! # Notations for probability theory

This file defines the following notations, for functions `X,Y`, measures `P, Q` defined on a
measurable space `m0`, and another measurable space structure `m` with `hm : m ≤ m0`,
- `P[X] = ∫ a, X a ∂P`
- `𝔼[X] = ∫ a, X a`
- `𝔼[X|m]`: conditional expectation of `X` with respect to the measure `volume` and the
  measurable space `m`. The similar `P[X|m]` for a measure `P` is defined in
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
-- We define notations `𝔼[f|m]` for the conditional expectation of `f` with respect to `m`.
localized [ProbabilityTheory] notation "𝔼[" X "|" m "]" => MeasureTheory.condexp m MeasureTheory.MeasureSpace.volume X

-- mathport name: «expr [ ]»
localized [ProbabilityTheory] notation P "[" X "]" => ∫ x, X x ∂P

-- mathport name: «expr𝔼[ ]»
localized [ProbabilityTheory] notation "𝔼[" X "]" => ∫ a, X a

-- mathport name: «expr =ₐₛ »
localized [ProbabilityTheory] notation:50 X " =ₐₛ " Y:50 => X =ᵐ[MeasureTheory.MeasureSpace.volume] Y

-- mathport name: «expr ≤ₐₛ »
localized [ProbabilityTheory] notation:50 X " ≤ₐₛ " Y:50 => X ≤ᵐ[MeasureTheory.MeasureSpace.volume] Y

-- mathport name: «expr∂ /∂ »
localized [ProbabilityTheory] notation "∂" P "/∂" Q:50 => P.rnDeriv Q

-- mathport name: «exprℙ»
localized [ProbabilityTheory] notation "ℙ" => MeasureTheory.MeasureSpace.volume

