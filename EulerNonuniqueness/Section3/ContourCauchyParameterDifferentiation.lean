import EulerNonuniqueness.Section3.ComplexContourVariationBounds
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem contourCauchyDensityRemainder_intervalIntegrable (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    IntervalIntegrable (contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target)
      volume (target - Real.pi) (target + Real.pi) := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mpr
  apply contourCauchyDensityRemainder_integrable_interval (norm_nonneg density) (norm_nonneg data)
    (sub_pos.mpr small) data.val.1.continuous data.val.2.val.1.continuous density.val.1.continuous
    (fun source _ => PeriodicHolderHalf.holder_bound density source target)
    (fun source _ => PeriodicC1HolderHalf.speed_bound data source)
  intro source inside
  apply PeriodicC1HolderHalf.chord_bound_extended data
  rw [abs_le]
  constructor <;> linarith [inside.1, inside.2, Real.pi_pos]

theorem contourCauchyTransform_hasDerivAt_complex_parameter (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius) (small : radius < 2 / (3 * Real.pi)) (target : ℝ) :
    HasDerivAt (fun parameter : ℂ => contourCauchyTransform (data + parameter • direction).val.1
      (data + parameter • direction).val.2.val.1 density.val.1 target)
      (∫ source in (target - Real.pi)..(target + Real.pi),
        (density.val.1 source - density.val.1 target) * contourCauchyKernelVariation data direction target source) 0 := by
  let radius_parameter := (radius - ‖data - standardCircleBanach‖) / (‖direction‖ + 1)
  have radius_positive : 0 < radius_parameter := div_pos (sub_pos.mpr near) (by positivity)
  let function : ℂ → ℝ → ℂ := fun parameter source => contourCauchyDensityRemainder
    (data + parameter • direction).val.1 (data + parameter • direction).val.2.val.1 density.val.1 target source
  let derivative : ℂ → ℝ → ℂ := fun parameter source =>
    (density.val.1 source - density.val.1 target) *
      contourCauchyKernelVariation (data + parameter • direction) direction target source
  let constant := (2 * (radius + ‖standardCircleBanach‖) * ‖direction‖ /
    (2 / (3 * Real.pi) - radius) ^ 2) * (2 * ‖density‖)
  have current_near (parameter : ℂ) (member : parameter ∈ Metric.ball 0 radius_parameter) :
      ‖data + parameter • direction - standardCircleBanach‖ < radius := by
    apply complexContourPerturbation_near data direction near
    simpa only [Metric.mem_ball, dist_zero_right, radius_parameter] using member
  have function_measurable (parameter : ℂ) : Measurable (function parameter) := by
    exact (((density.val.1.continuous.measurable.sub measurable_const).mul
      (data + parameter • direction).val.2.val.1.continuous.measurable).div
        (measurable_const.sub (data + parameter • direction).val.1.continuous.measurable))
  have derivative_measurable : Measurable (derivative 0) :=
    (density.val.1.continuous.measurable.sub measurable_const).mul
      (measurable_contourCauchyKernelVariation (data + (0 : ℂ) • direction) direction target)
  have initial_integrable : IntervalIntegrable (function 0) volume (target - Real.pi) (target + Real.pi) := by
    simpa only [function, zero_smul, add_zero] using
      contourCauchyDensityRemainder_intervalIntegrable data density (near.trans small) target
  have bound_integrable : IntervalIntegrable (fun source => constant * inverseSqrtDistance target source)
      volume (target - Real.pi) (target + Real.pi) :=
    (inverseSqrtDistance_integrable_centered target Real.pi_pos).const_mul constant
  suffices integral_derivative : HasDerivAt (fun parameter => ∫ source in (target - Real.pi)..(target + Real.pi), function parameter source)
      (∫ source in (target - Real.pi)..(target + Real.pi), derivative 0 source) (0 : ℂ) by
    have result := integral_derivative.sub_const ((Real.pi : ℂ) * Complex.I * density.val.1 target)
    simpa only [contourCauchyTransform, function, derivative, zero_smul, add_zero] using result
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := function) (F' := derivative) (μ := volume) (x₀ := (0 : ℂ))
    (a := target - Real.pi) (b := target + Real.pi)
    (bound := fun source => constant * inverseSqrtDistance target source)
    radius_positive (Eventually.of_forall fun parameter => (function_measurable parameter).aestronglyMeasurable)
    initial_integrable derivative_measurable.aestronglyMeasurable _ bound_integrable _).2
  · exact Eventually.of_forall fun source member parameter parameter_member => by
      have inside : source ∈ Icc (target - Real.pi) (target + Real.pi) := by
        rw [uIoc_of_le (by linarith [Real.pi_pos])] at member
        exact ⟨member.1.le, member.2⟩
      have variation_bound := contourCauchyKernelVariation_uniform_majorized
        (data + parameter • direction) direction small (current_near parameter parameter_member).le target inside
      have density_bound : ‖density.val.1 source - density.val.1 target‖ ≤ 2 * ‖density‖ :=
        (norm_sub_le _ _).trans (by linarith [PeriodicHolderHalf.value_bound density source,
          PeriodicHolderHalf.value_bound density target])
      dsimp only [derivative]
      rw [norm_mul]
      have estimate := mul_le_mul density_bound variation_bound (norm_nonneg _) (by positivity)
      exact estimate.trans_eq (by dsimp only [constant]; ring)
  · exact Eventually.of_forall fun source member parameter parameter_member => by
      by_cases equal : source = target
      · subst source
        simpa only [function, derivative, contourCauchyDensityRemainder, contourCauchyKernelVariation,
          sub_self, zero_mul, zero_div, div_zero, sub_zero] using hasDerivAt_const parameter (0 : ℂ)
      · have inside : source ∈ Icc (target - Real.pi) (target + Real.pi) := by
          rw [uIoc_of_le (by linarith [Real.pi_pos])] at member
          exact ⟨member.1.le, member.2⟩
        have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
          rw [abs_le]
          constructor <;> linarith [inside.1, inside.2, Real.pi_pos]
        have current_small := (current_near parameter parameter_member).trans small
        have separated : (data + parameter • direction).val.1 target -
            (data + parameter • direction).val.1 source ≠ 0 := by
          apply norm_ne_zero_iff.mp
          exact ((mul_pos (sub_pos.mpr current_small) (abs_pos.mpr (sub_ne_zero.mpr equal))).trans_le
            (PeriodicC1HolderHalf.chord_bound_extended (data + parameter • direction) nearby)).ne'
        have kernel_derivative := (contourCauchyKernel_hasDerivAt_complex_parameter data direction parameter separated).const_mul
          (density.val.1 source - density.val.1 target)
        simpa only [function, derivative, contourCauchyDensityRemainder, contourCauchyKernel, mul_div_assoc]
          using kernel_derivative

end

end EulerNonuniqueness.Paper
