import EulerNonuniqueness.Section3.NearCircleSpacetimeDifferentiation
import EulerNonuniqueness.Section3.AffinePatchDomain
import EulerNonuniqueness.Section3.FiniteLiteralPatchFlow

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem continuous_nearCircleInterior_spacetime_integral
    (shape : ℝ → PeriodicC1HolderHalf) (shape_continuous : Continuous shape)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3)
    (function : ℝ × ℂ → ℝ) (function_continuous : Continuous function) :
    Continuous (fun parameter => ∫ position in nearCircleInterior (shape parameter) (small parameter),
      function (parameter, position)) := by
  let integrand : (ℝ × ℝ) → ℝ → ℝ := fun pair scale =>
    scale * function (pair.1, scale • (shape pair.1).val.1 pair.2) *
      contourAreaPair ((shape pair.1).val.1 pair.2) ((shape pair.1).val.2.val.1 pair.2)
  have curve_continuous := continuous_contour_value_joint shape shape_continuous
  have tangent_continuous := continuous_contour_tangent_joint shape shape_continuous
  have integrand_continuous : Continuous (Function.uncurry integrand) := by
    have curve_lift := curve_continuous.comp (continuous_fst : Continuous (fun triple : (ℝ × ℝ) × ℝ => triple.1))
    have tangent_lift := tangent_continuous.comp (continuous_fst : Continuous (fun triple : (ℝ × ℝ) × ℝ => triple.1))
    exact (continuous_snd.mul (function_continuous.comp
      ((continuous_fst.fst).prodMk (continuous_snd.smul curve_lift)))).mul
        (continuous_contourAreaPair.comp (curve_lift.prodMk tangent_lift))
  have inner_continuous : Continuous (fun pair : ℝ × ℝ => ∫ scale in (0 : ℝ)..1, integrand pair scale) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
      integrand_continuous continuous_const
  have outer_continuous : Continuous (fun parameter => ∫ label in (-Real.pi)..Real.pi,
      ∫ scale in (0 : ℝ)..1, integrand (parameter, label) scale) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
      inner_continuous continuous_const
  convert outer_continuous using 1
  funext parameter
  rw [integral_nearCircleInterior_radial_flux (shape parameter) (small parameter)
    (fun position => function (parameter, position))
    (function_continuous.comp (continuous_const.prodMk continuous_id))]
  apply intervalIntegral.integral_congr
  intro label _
  change contourAreaPair ((shape parameter).val.1 label) ((shape parameter).val.2.val.1 label) *
    (∫ scale in (0 : ℝ)..1, scale * function (parameter, scale • (shape parameter).val.1 label)) = _
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro scale _
  dsimp only [integrand]
  ring

theorem continuous_affinePatchDomain_spacetime_integral
    (center : ℂ) {scale : ℝ} (positive : 0 < scale)
    (shape : ℝ → PeriodicC1HolderHalf) (shape_continuous : Continuous shape)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3)
    (function : ℝ × ℂ → ℝ) (function_continuous : Continuous function) :
    Continuous (fun parameter => ∫ position in affinePatchDomain center scale (shape parameter) (small parameter),
      function (parameter, position)) := by
  have pulled_continuous : Continuous (fun pair : ℝ × ℂ => function (pair.1, center + scale • pair.2)) := by
    fun_prop
  have result := (continuous_const : Continuous (fun _ : ℝ => scale ^ 2)).mul (continuous_nearCircleInterior_spacetime_integral shape shape_continuous small
    (fun pair => function (pair.1, center + scale • pair.2)) pulled_continuous)
  change Continuous (fun parameter => scale ^ 2 * ∫ position in nearCircleInterior (shape parameter) (small parameter),
    function (parameter, center + scale • position)) at result
  convert result using 1
  funext parameter
  exact integral_affinePatchDomain center positive (shape parameter) (small parameter)
    (fun position => function (parameter, position))

theorem FiniteLiteralPatchFlow.continuous_domain_spacetime_integral {count : ℕ}
    {configuration : FiniteContourConfiguration count} (flow : FiniteLiteralPatchFlow configuration)
    (index : Fin count) (function : ℝ × ℂ → ℝ) (function_continuous : Continuous function) :
    Continuous (fun parameter => ∫ position in flow.domain parameter index, function (parameter, position)) :=
  continuous_affinePatchDomain_spacetime_integral (configuration.center index) (configuration.radius_pos index)
    (fun parameter => flow.shape parameter index) ((continuous_apply index).comp flow.continuous)
    (fun parameter => (flow.nearby parameter index).trans_le (min_le_left _ _)) function function_continuous

end

end EulerNonuniqueness.Paper
