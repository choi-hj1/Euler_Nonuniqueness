import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

theorem hasDerivAt_continuous_operator_apply_zero
    {Domain Range : Type*} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Range] [NormedSpace ℝ Range]
    {operator : ℝ → Domain →L[ℝ] Range} {path : ℝ → Domain}
    {time : ℝ} {velocity : Domain}
    (operatorContinuous : ContinuousAt operator time)
    (pathDerivative : HasDerivAt path velocity time) (pathZero : path time = 0) :
    HasDerivAt (fun current => operator current (path current)) (operator time velocity) time := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have operatorLimit : Tendsto operator (𝓝[≠] time) (𝓝 (operator time)) :=
    operatorContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have pathLimit := hasDerivAt_iff_tendsto_slope.mp pathDerivative
  have applied := isBoundedBilinearMap_apply.continuous.tendsto (operator time, velocity)
  have result := applied.comp (operatorLimit.prodMk_nhds pathLimit)
  convert result using 1
  funext current
  simp only [Function.comp_def, slope_def_module, pathZero, map_zero, sub_zero, map_smul]

end EulerNonuniqueness.General
