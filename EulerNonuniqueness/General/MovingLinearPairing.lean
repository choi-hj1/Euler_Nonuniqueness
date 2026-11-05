import EulerNonuniqueness.General.ConvolutionContinuity

noncomputable section

open Filter
open scoped Topology

namespace ContinuousLinearMap

theorem tendsto_apply_moving_of_bounded
    {Domain Value Index : Type*} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {filter : Filter Index} {operators : Index → Domain →L[ℝ] Value}
    {arguments : Index → Domain} {argument : Domain} {value : Value} {bound : ℝ}
    (bounded : ∀ index, ‖operators index‖ ≤ bound)
    (fixedConverges : Tendsto (fun index => operators index argument) filter (𝓝 value))
    (argumentsConverge : Tendsto arguments filter (𝓝 argument)) :
    Tendsto (fun index => operators index (arguments index)) filter (𝓝 value) := by
  have normDifference : Tendsto (fun index => ‖arguments index - argument‖) filter (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (argumentsConverge.sub (tendsto_const_nhds (x := argument))).norm
  have errorBound (index : Index) :
      ‖operators index (arguments index - argument)‖ ≤ max bound 0 * ‖arguments index - argument‖ :=
    ((operators index).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((bounded index).trans (le_max_left bound 0)) (norm_nonneg _))
  have error : Tendsto (fun index => operators index (arguments index - argument)) filter (𝓝 0) := by
    apply squeeze_zero_norm errorBound
    simpa only [mul_zero] using normDifference.const_mul (max bound 0)
  have expansion (index : Index) :
      operators index (arguments index - argument) + operators index argument =
        operators index (arguments index) := by rw [map_sub, sub_add_cancel]
  simpa only [zero_add, expansion] using error.add fixedConverges

end ContinuousLinearMap
