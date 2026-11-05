import EulerNonuniqueness.Section3.ContourSecondVariationUniformDifference
import EulerNonuniqueness.General.HolomorphicJetLimit

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondVariationBilinearHolderComplexSpace
  secondVariationBilinearC1ComplexSpace secondVariationBilinearOperatorGroup
  secondVariationBilinearOperatorSpace

theorem contourCauchySecondVariation_differentiableOn_complex_line
    (data direction first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {domain : Set ℂ} (openDomain : IsOpen domain) {innerRadius outerRadius : ℝ}
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ∀ point ∈ domain,
      ‖data + point • direction - standardCircleBanach‖ ≤ innerRadius) :
    DifferentiableOn ℂ (fun point : ℂ =>
      contourCauchySecondVariation (data + point • direction) first second density) domain := by
  let step := (outerRadius - innerRadius) /
    (4 * (‖first + second‖ + ‖first‖ + ‖second‖ + 1))
  have stepPositive : 0 < step := div_pos (sub_pos.mpr gap) (by positivity)
  have smallParameters : ∀ᶠ parameter in 𝓝[≠] (0 : ℂ), ‖parameter‖ < step := by
    have actual : ∀ᶠ parameter in 𝓝 (0 : ℂ), parameter ∈ ball 0 step :=
      ball_mem_nhds 0 stepPositive
    simpa only [mem_ball, dist_zero_right] using actual.filter_mono nhdsWithin_le_nhds
  have shifts (parameter : ℂ) (parameterSmall : ‖parameter‖ < step) :
      ‖parameter • (first + second)‖ ≤ (outerRadius - innerRadius) / 4 ∧
      ‖parameter • first‖ ≤ (outerRadius - innerRadius) / 4 ∧
      ‖parameter • second‖ ≤ (outerRadius - innerRadius) / 4 := by
    have product : ‖parameter‖ *
        (‖first + second‖ + ‖first‖ + ‖second‖ + 1) < (outerRadius - innerRadius) / 4 := by
      have bound := (lt_div_iff₀ (by positivity :
        0 < 4 * (‖first + second‖ + ‖first‖ + ‖second‖ + 1))).mp parameterSmall
      nlinarith
    have sumNorm : ‖parameter • (first + second)‖ = ‖parameter‖ * ‖first + second‖ := by
      with_reducible exact norm_smul parameter (first + second)
    have firstNorm : ‖parameter • first‖ = ‖parameter‖ * ‖first‖ := by
      with_reducible exact norm_smul parameter first
    have secondNorm : ‖parameter • second‖ = ‖parameter‖ * ‖second‖ := by
      with_reducible exact norm_smul parameter second
    rw [sumNorm, firstNorm, secondNorm]
    constructor
    · nlinarith [norm_nonneg parameter, norm_nonneg first, norm_nonneg second]
    constructor
    · nlinarith [norm_nonneg parameter, norm_nonneg (first + second), norm_nonneg second]
    · nlinarith [norm_nonneg parameter, norm_nonneg (first + second), norm_nonneg first]
  let approximant := fun parameter point : ℂ => (parameter ^ 2)⁻¹ •
    (extendedContourCauchy (data + point • direction + parameter • (first + second)) density -
      extendedContourCauchy (data + point • direction + parameter • first) density -
      extendedContourCauchy (data + point • direction + parameter • second) density +
      extendedContourCauchy (data + point • direction) density)
  apply EulerNonuniqueness.General.differentiableOn_of_uniform_linear_error
    approximant _ domain openDomain
    (constant := (16 * (contourCauchyUniformOperatorConstant outerRadius * ‖density‖) /
      (outerRadius - innerRadius) ^ 3) *
        (‖first + second‖ ^ 3 + ‖first‖ ^ 3 + ‖second‖ ^ 3))
  · filter_upwards [smallParameters, self_mem_nhdsWithin] with parameter parameterSmall nonzero
    intro point member
    have parameterNonzero : parameter ≠ 0 := nonzero
    have shifted := shifts parameter parameterSmall
    have bound := contourCauchySecondVariation_uniform_mixed_difference_bound
      (data + point • direction) first second density (nearby point member) gap small
      parameterNonzero shifted.1 shifted.2.1 shifted.2.2
    exact bound.trans_eq (by ring)
  · filter_upwards [smallParameters] with parameter parameterSmall
    have shifted := shifts parameter parameterSmall
    have curve (increment : PeriodicC1HolderHalf)
        (incrementSmall : ‖increment‖ ≤ (outerRadius - innerRadius) / 4) :
        DifferentiableOn ℂ (fun point : ℂ =>
          extendedContourCauchy (data + point • direction + increment) density) domain := by
      intro point member
      have perturbed : ‖data + increment + point • direction - standardCircleBanach‖ <
          min 1 (2 / (3 * Real.pi)) := by
        have identity : data + increment + point • direction - standardCircleBanach =
            (data + point • direction - standardCircleBanach) + increment := by abel
        rw [identity]
        apply ((norm_add_le _ _).trans (add_le_add (nearby point member) incrementSmall)).trans_lt
        linarith
      have actual := extendedContourCauchy_differentiableAt_complex_line
        (data + increment) direction density point perturbed
      have reordered : (fun current : ℂ =>
          extendedContourCauchy (data + current • direction + increment) density) =
          (fun current : ℂ =>
            extendedContourCauchy (data + increment + current • direction) density) := by
        funext current
        apply congrArg (fun shape => extendedContourCauchy shape density)
        abel
      rw [reordered]
      exact actual.differentiableWithinAt
    have unshifted : DifferentiableOn ℂ (fun point : ℂ =>
        extendedContourCauchy (data + point • direction) density) domain := by
      intro point member
      exact (extendedContourCauchy_differentiableAt_complex_line data direction density point
        ((nearby point member).trans_lt (gap.trans small))).differentiableWithinAt
    exact (((curve _ shifted.1).sub (curve _ shifted.2.1)).sub
      (curve _ shifted.2.2) |>.add unshifted).const_smul _

end

end EulerNonuniqueness.Paper
