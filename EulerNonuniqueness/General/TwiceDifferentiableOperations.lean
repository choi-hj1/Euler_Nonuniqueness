import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {Domain Value Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Value] [NormedSpace ℝ Value]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem differentiableAt_fderiv_composition
    (function : Value → Range) (chart : Domain → Value) (base : Domain)
    (firstFunction : ∀ᶠ point in 𝓝 (chart base), DifferentiableAt ℝ function point)
    (firstChart : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ chart point)
    (secondFunction : DifferentiableAt ℝ (fderiv ℝ function) (chart base))
    (secondChart : DifferentiableAt ℝ (fderiv ℝ chart) base) :
    DifferentiableAt ℝ (fderiv ℝ (fun point => function (chart point))) base := by
  have chartActual : DifferentiableAt ℝ chart base := firstChart.self_of_nhds
  have composedSecond := secondFunction.comp base chartActual
  have expression := composedSecond.clm_comp secondChart
  apply expression.congr_of_eventuallyEq
  filter_upwards [firstChart, chartActual.continuousAt.tendsto.eventually firstFunction] with point chartDerivative functionDerivative
  exact fderiv_comp point functionDerivative chartDerivative

theorem differentiableAt_fderiv_operator_apply
    (coefficient : Domain → Value →L[ℝ] Range) (value : Domain → Value) (base : Domain)
    (firstCoefficient : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ coefficient point)
    (firstValue : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ value point)
    (secondCoefficient : DifferentiableAt ℝ (fderiv ℝ coefficient) base)
    (secondValue : DifferentiableAt ℝ (fderiv ℝ value) base) :
    DifferentiableAt ℝ (fderiv ℝ (fun point => coefficient point (value point))) base := by
  have coefficientActual : DifferentiableAt ℝ coefficient base := firstCoefficient.self_of_nhds
  have valueActual : DifferentiableAt ℝ value base := firstValue.self_of_nhds
  have firstTerm : DifferentiableAt ℝ
      (fun point => (coefficient point).comp (fderiv ℝ value point)) base :=
    DifferentiableAt.clm_comp (𝕜 := ℝ) (E := Domain) (F := Domain) (G := Value) (H := Range)
      coefficientActual secondValue
  let flipMap : (Domain →L[ℝ] Value →L[ℝ] Range) →L[ℝ] Value →L[ℝ] Domain →L[ℝ] Range :=
    (ContinuousLinearMap.flipₗᵢ ℝ Domain Value Range).toContinuousLinearEquiv.toContinuousLinearMap
  have flipDerivative : HasFDerivAt flipMap flipMap (fderiv ℝ coefficient base) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Domain →L[ℝ] Value →L[ℝ] Range)
      (F := Value →L[ℝ] Domain →L[ℝ] Range) flipMap
  have flipped : DifferentiableAt ℝ (fun point => (fderiv ℝ coefficient point).flip) base := by
    change DifferentiableAt ℝ (fun point => flipMap (fderiv ℝ coefficient point)) base
    exact (HasFDerivAt.comp (𝕜 := ℝ) (E := Domain) (F := Domain →L[ℝ] Value →L[ℝ] Range)
      (G := Value →L[ℝ] Domain →L[ℝ] Range) base flipDerivative secondCoefficient.hasFDerivAt).differentiableAt
  have secondTerm : DifferentiableAt ℝ
      (fun point => (fderiv ℝ coefficient point).flip (value point)) base :=
    DifferentiableAt.clm_apply (𝕜 := ℝ) (E := Domain) (G := Value) (H := Domain →L[ℝ] Range)
      flipped valueActual
  apply (firstTerm.add secondTerm).congr_of_eventuallyEq
  filter_upwards [firstCoefficient, firstValue] with point coefficientDerivative valueDerivative
  exact fderiv_clm_apply coefficientDerivative valueDerivative

theorem differentiableAt_fderiv_sub_linear
    (function : Domain → Range) (linear : Domain →L[ℝ] Range) (base : Domain)
    (first : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ function point)
    (second : DifferentiableAt ℝ (fderiv ℝ function) base) :
    DifferentiableAt ℝ (fderiv ℝ (fun point => function point - linear point)) base := by
  apply (second.sub_const linear).congr_of_eventuallyEq
  filter_upwards [first] with point actual
  exact (actual.hasFDerivAt.sub linear.hasFDerivAt).fderiv

theorem differentiableAt_fderiv_pullback
    (field : Value → Value) (chart : Domain → Value)
    (coefficient : Domain → Value →L[ℝ] Value) (base : Domain)
    (firstField : ∀ᶠ point in 𝓝 (chart base), DifferentiableAt ℝ field point)
    (firstChart : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ chart point)
    (firstCoefficient : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ coefficient point)
    (secondField : DifferentiableAt ℝ (fderiv ℝ field) (chart base))
    (secondChart : DifferentiableAt ℝ (fderiv ℝ chart) base)
    (secondCoefficient : DifferentiableAt ℝ (fderiv ℝ coefficient) base) :
    DifferentiableAt ℝ (fderiv ℝ (fun point => coefficient point (field (chart point)))) base := by
  have chartActual : DifferentiableAt ℝ chart base := firstChart.self_of_nhds
  have firstComposed : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ (fun point => field (chart point)) point := by
    filter_upwards [firstChart, chartActual.continuousAt.tendsto.eventually firstField] with point chartDerivative fieldDerivative
    exact fieldDerivative.comp point chartDerivative
  exact differentiableAt_fderiv_operator_apply coefficient (fun point => field (chart point)) base
    firstCoefficient firstComposed secondCoefficient
    (differentiableAt_fderiv_composition field chart base firstField firstChart secondField secondChart)

end

end EulerNonuniqueness.General
