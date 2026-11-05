import EulerNonuniqueness.Section3.FiniteLiteralPatchMoments
import EulerNonuniqueness.Section3.AffinePatchSpacetimeReynolds

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem domain_spacetime_integral_hasDerivAt (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter => ∫ position in flow.domain parameter index, function (parameter, position))
      ((∫ position in flow.domain time index, derivative (time, position) (1, 0)) +
        ∫ position in flow.domain time index,
          derivative (time, position) (0, biotSavart (flow.vorticity time) position)) time := by
  let radius := min (time + flow.duration) (flow.duration - time)
  have radius_positive : 0 < radius := lt_min (by linarith [inside.1]) (by linarith [inside.2])
  have ball_inside : ∀ parameter ∈ Metric.ball time radius, parameter ∈ Ioo (-flow.duration) flow.duration := by
    intro parameter close
    have distance : |parameter - time| < radius := by simpa only [Metric.mem_ball, Real.dist_eq] using close
    have lower := min_le_left (time + flow.duration) (flow.duration - time)
    have upper := min_le_right (time + flow.duration) (flow.duration - time)
    dsimp only [radius] at distance
    constructor <;> linarith [(abs_lt.mp distance).1, (abs_lt.mp distance).2]
  have result := affinePatchDomain_hasDerivAt_spacetime_Reynolds (configuration.center index)
    (configuration.radius_pos index) (fun parameter => flow.shape parameter index)
    (fun parameter => configuration.vectorField (flow.shape parameter) index)
    ((continuous_apply index).comp flow.continuous) ((continuous_apply index).comp flow.velocity_continuous)
    (fun parameter => (flow.nearby parameter index).trans_le (min_le_left _ _)) time radius radius_positive
    (fun parameter close => flow.shape_component_hasDerivAt (ball_inside parameter close) index)
    function derivative function_continuous derivative_continuous function_derivative
  let spatial : ℂ → ℂ →L[ℝ] ℝ := fun position =>
    (derivative (time, position)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)
  have spatial_continuous : Continuous spatial :=
    (derivative_continuous.comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  have flux_identity := integral_affinePatchDomain_biotSavart_advection (configuration.center index)
    (configuration.radius_pos index) (flow.shape time index)
    ((flow.nearby time index).trans_le (min_le_left _ _)) (fun position => function (time, position)) spatial
    (function_continuous.comp (continuous_const.prodMk continuous_id)) spatial_continuous
    (fun position => (function_derivative _).comp position (hasFDerivAt_prodMk_right time position))
    (flow.vorticity_integrable time) (flow.vorticity_memLp time (ENNReal.ofReal (4 : ℝ)))
  have coefficient_identity :
      (∫ position in flow.domain time index, derivative (time, position)
        (0, biotSavart (flow.vorticity time) position)) =
      ∫ label in (-Real.pi)..Real.pi,
        function (time, configuration.center index + configuration.radius index • (flow.shape time index).val.1 label) *
          contourAreaPair (configuration.radius index • (configuration.vectorField (flow.shape time) index).val.1 label)
            (configuration.radius index • (flow.shape time index).val.2.val.1 label) := by
    change (∫ position in flow.domain time index, spatial position (biotSavart (flow.vorticity time) position)) = _
    dsimp only [domain, FiniteContourConfiguration.literalDomain]
    rw [flux_identity]
    apply intervalIntegral.integral_congr
    intro label _
    dsimp only
    congr 2
    exact flow.velocity_eq time index label
  rw [coefficient_identity]
  exact result

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
