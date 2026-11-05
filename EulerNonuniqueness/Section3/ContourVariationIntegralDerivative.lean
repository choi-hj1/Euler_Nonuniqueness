import EulerNonuniqueness.Section3.ContourQuadraticUniformBound
import EulerNonuniqueness.Section3.ContourKernelSecondDerivative
import EulerNonuniqueness.Section3.ContourCauchyDirectionalDerivative
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem contourCauchyVariationIntegral_hasDerivAt_parameter
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < 2 / (3 * Real.pi)) (target : ℝ) :
    HasDerivAt (fun parameter : ℂ =>
      ∫ source in (target - Real.pi)..(target + Real.pi),
        (density.val.1 source - density.val.1 target) *
          contourCauchyKernelVariation (data + parameter • second) first target source)
      (2 * contourCauchyQuadraticIntegral data first second density target) 0 := by
  let parameterRadius := (radius - ‖data - standardCircleBanach‖) / (‖second‖ + 1)
  have positive : 0 < parameterRadius := div_pos (sub_pos.mpr near) (by positivity)
  let function : ℂ → ℝ → ℂ := fun parameter source =>
    (density.val.1 source - density.val.1 target) *
      contourCauchyKernelVariation (data + parameter • second) first target source
  let derivative : ℂ → ℝ → ℂ := fun parameter source =>
    (density.val.1 source - density.val.1 target) *
      (2 * contourCauchyKernelQuadratic (data + parameter • second) first second target source)
  let constant := (4 * (radius + ‖standardCircleBanach‖) * ‖first‖ * ‖second‖ /
    (2 / (3 * Real.pi) - radius) ^ 3) * (2 * ‖density‖)
  have current_near (parameter : ℂ) (member : parameter ∈ Metric.ball 0 parameterRadius) :
      ‖data + parameter • second - standardCircleBanach‖ < radius := by
    apply complexContourPerturbation_near data second near
    simpa only [Metric.mem_ball, dist_zero_right, parameterRadius] using member
  have function_measurable (parameter : ℂ) : Measurable (function parameter) :=
    (density.val.1.continuous.measurable.sub measurable_const).mul
      (measurable_contourCauchyKernelVariation (data + parameter • second) first target)
  have derivative_measurable : Measurable (derivative 0) :=
    (density.val.1.continuous.measurable.sub measurable_const).mul
      (measurable_const.mul
        (measurable_contourCauchyKernelQuadratic (data + (0 : ℂ) • second) first second target))
  have initial_integrable : IntervalIntegrable (function 0) volume
      (target - Real.pi) (target + Real.pi) := by
    simpa only [function, zero_smul, add_zero] using
      contourCauchyKernelVariation_density_integrable data first density (near.trans small) target
  have bound_integrable : IntervalIntegrable (fun source => constant * inverseSqrtDistance target source)
      volume (target - Real.pi) (target + Real.pi) :=
    (inverseSqrtDistance_integrable_centered target Real.pi_pos).const_mul constant
  have actual := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := function) (F' := derivative) (μ := volume) (x₀ := (0 : ℂ))
    (a := target - Real.pi) (b := target + Real.pi)
    (bound := fun source => constant * inverseSqrtDistance target source)
    positive (Eventually.of_forall fun parameter => (function_measurable parameter).aestronglyMeasurable)
    initial_integrable derivative_measurable.aestronglyMeasurable ?_ bound_integrable ?_).2
  · convert actual using 1
    dsimp only [derivative]
    simp only [zero_smul, add_zero]
    unfold contourCauchyQuadraticIntegral
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext source
    ring
  · exact Eventually.of_forall fun source member parameter parameter_member => by
      have inside : source ∈ Icc (target - Real.pi) (target + Real.pi) := by
        rw [uIoc_of_le (by linarith [Real.pi_pos])] at member
        exact ⟨member.1.le, member.2⟩
      have bound := contourCauchyKernelQuadratic_uniform_majorized
        (data + parameter • second) first second small
        (current_near parameter parameter_member).le target inside
      have density_bound : ‖density.val.1 source - density.val.1 target‖ ≤ 2 * ‖density‖ :=
        (norm_sub_le _ _).trans (by linarith [PeriodicHolderHalf.value_bound density source,
          PeriodicHolderHalf.value_bound density target])
      dsimp only [derivative]
      rw [norm_mul, norm_mul]
      norm_num only [Complex.norm_ofNat]
      have estimate := mul_le_mul density_bound
        (mul_le_mul_of_nonneg_left bound (by norm_num : (0 : ℝ) ≤ 2))
        (by positivity) (by positivity)
      exact estimate.trans_eq (by dsimp only [constant]; ring)
  · exact Eventually.of_forall fun source member parameter parameter_member => by
      by_cases equal : source = target
      · subst source
        simpa only [function, derivative, sub_self, zero_mul] using
          hasDerivAt_const parameter (0 : ℂ)
      · have inside : source ∈ Icc (target - Real.pi) (target + Real.pi) := by
          rw [uIoc_of_le (by linarith [Real.pi_pos])] at member
          exact ⟨member.1.le, member.2⟩
        have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
          rw [abs_le]
          constructor <;> linarith [inside.1, inside.2, Real.pi_pos]
        have current_small := (current_near parameter parameter_member).trans small
        have separated : (data + parameter • second).val.1 target -
            (data + parameter • second).val.1 source ≠ 0 := by
          apply norm_ne_zero_iff.mp
          exact ((mul_pos (sub_pos.mpr current_small)
            (abs_pos.mpr (sub_ne_zero.mpr equal))).trans_le
              (PeriodicC1HolderHalf.chord_bound_extended (data + parameter • second) nearby)).ne'
        exact (contourCauchyKernelVariation_hasDerivAt_complex_parameter
          data first second parameter separated).const_mul
            (density.val.1 source - density.val.1 target)

end

end EulerNonuniqueness.Paper
