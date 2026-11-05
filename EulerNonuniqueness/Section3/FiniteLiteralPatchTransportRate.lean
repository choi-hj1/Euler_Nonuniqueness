import EulerNonuniqueness.Section3.FiniteLiteralPatchSpacetime
import EulerNonuniqueness.Section3.SpacetimePatchContinuity

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

def fluxTransportRate (flow : FiniteLiteralPatchFlow configuration) (index : Fin count)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ) (time : ℝ) : ℝ :=
  (∫ position in flow.domain time index, derivative (time, position) (1, 0)) +
    ∫ label in (-Real.pi)..Real.pi,
      function (time, configuration.center index + configuration.radius index • (flow.shape time index).val.1 label) *
        contourAreaPair (configuration.radius index • (configuration.vectorField (flow.shape time) index).val.1 label)
          (configuration.radius index • (flow.shape time index).val.2.val.1 label)

theorem continuous_fluxTransportRate (flow : FiniteLiteralPatchFlow configuration) (index : Fin count)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative) :
    Continuous (flow.fluxTransportRate index function derivative) := by
  have temporal_continuous : Continuous (fun pair : ℝ × ℂ => derivative pair (1, (0 : ℂ))) :=
    derivative_continuous.clm_apply continuous_const
  have temporal := flow.continuous_domain_spacetime_integral index _ temporal_continuous
  have shape_continuous := (continuous_apply index).comp flow.continuous
  have velocity_continuous := (continuous_apply index).comp flow.velocity_continuous
  have curve := continuous_contour_value_joint (fun time => flow.shape time index) shape_continuous
  have tangent := continuous_contour_tangent_joint (fun time => flow.shape time index) shape_continuous
  have velocity := continuous_contour_value_joint
    (fun time => configuration.vectorField (flow.shape time) index) velocity_continuous
  have integrand_continuous : Continuous (fun pair : ℝ × ℝ =>
      function (pair.1, configuration.center index + configuration.radius index • (flow.shape pair.1 index).val.1 pair.2) *
        contourAreaPair (configuration.radius index • (configuration.vectorField (flow.shape pair.1) index).val.1 pair.2)
          (configuration.radius index • (flow.shape pair.1 index).val.2.val.1 pair.2)) :=
    (function_continuous.comp (continuous_fst.prodMk (continuous_const.add (continuous_const.smul curve)))).mul
      (continuous_contourAreaPair.comp ((continuous_const.smul velocity).prodMk (continuous_const.smul tangent)))
  exact temporal.add (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) integrand_continuous continuous_const)

theorem domain_spacetime_integral_hasDerivAt_flux (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter => ∫ position in flow.domain parameter index, function (parameter, position))
      (flow.fluxTransportRate index function derivative time) time := by
  let radius := min (time + flow.duration) (flow.duration - time)
  have radius_positive : 0 < radius := lt_min (by linarith [inside.1]) (by linarith [inside.2])
  have ball_inside : ∀ parameter ∈ Metric.ball time radius, parameter ∈ Ioo (-flow.duration) flow.duration := by
    intro parameter close
    have distance : |parameter - time| < radius := by simpa only [Metric.mem_ball, Real.dist_eq] using close
    have lower := min_le_left (time + flow.duration) (flow.duration - time)
    have upper := min_le_right (time + flow.duration) (flow.duration - time)
    dsimp only [radius] at distance
    constructor <;> linarith [(abs_lt.mp distance).1, (abs_lt.mp distance).2]
  exact affinePatchDomain_hasDerivAt_spacetime_Reynolds (configuration.center index)
    (configuration.radius_pos index) (fun parameter => flow.shape parameter index)
    (fun parameter => configuration.vectorField (flow.shape parameter) index)
    ((continuous_apply index).comp flow.continuous) ((continuous_apply index).comp flow.velocity_continuous)
    (fun parameter => (flow.nearby parameter index).trans_le (min_le_left _ _)) time radius radius_positive
    (fun parameter close => flow.shape_component_hasDerivAt (ball_inside parameter close) index)
    function derivative function_continuous derivative_continuous function_derivative

theorem fluxTransportRate_eq_actual (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ point, HasFDerivAt function (derivative point) point) :
    flow.fluxTransportRate index function derivative time =
      (∫ position in flow.domain time index, derivative (time, position) (1, 0)) +
        ∫ position in flow.domain time index,
          derivative (time, position) (0, biotSavart (flow.vorticity time) position) :=
  (flow.domain_spacetime_integral_hasDerivAt_flux inside index function derivative function_continuous
    derivative_continuous function_derivative).unique
      (flow.domain_spacetime_integral_hasDerivAt inside index function derivative function_continuous
        derivative_continuous function_derivative)

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
