import EulerNonuniqueness.Section3.ContourThirdOperatorRemainder
import EulerNonuniqueness.General.DirectionalCandidateAdditivity

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondOperatorLipHolderModule secondOperatorLipC1Module
  derivativeOperatorHolderSpace derivativeOperatorC1Space
  derivativeOperatorGroup derivativeOperatorModule derivativeOperatorSpace
  derivativeDensityOperatorGroup derivativeDensityOperatorModule derivativeDensityOperatorSpace
  secondFamilyDerivativeGroup secondFamilyDerivativeSub secondLineDerivativeAddCommGroup
  secondLineDensityContinuousAdd secondLineDerivativeModule secondLineDerivativeSpace
  secondHolomorphicOperatorComplete secondHolomorphicDensityComplete secondHolomorphicFamilyComplete
  higherCauchyOperatorSMul higherCauchyDensitySMul higherCauchyFamilySMul higherCauchyFamilyBoundedSMul
  higherCauchyFamilyUniformity higherCauchyFamilyTopology higherCauchyFamilyContinuousSMul
  thirdRemainderFamilySub thirdRemainderFamilySMul

theorem contourCauchyThirdDirectionalOperator_add
    (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourCauchyThirdDirectionalOperator data (first + second) =
      contourCauchyThirdDirectionalOperator data first + contourCauchyThirdDirectionalOperator data second := by
  obtain ⟨innerRadius, near, innerSmall⟩ := exists_between small
  obtain ⟨outerRadius, gap, outerSmall⟩ := exists_between innerSmall
  let remainderConstant := 512 * contourCauchyParameterOperatorConstant outerRadius /
    (outerRadius - innerRadius) ^ 3
  let variationConstant := 256 * contourCauchyParameterOperatorConstant outerRadius /
    (outerRadius - innerRadius) ^ 3
  let step := min ((innerRadius - ‖data - standardCircleBanach‖) / (‖first‖ + 1))
    ((outerRadius - innerRadius) / (8 * (‖first‖ + ‖second‖ + ‖first + second‖ + 1)))
  have stepPositive : 0 < step := by
    apply lt_min
    · exact div_pos (sub_pos.mpr near) (by positivity)
    · exact div_pos (sub_pos.mpr gap) (by positivity)
  have smallParameters : ∀ᶠ parameter in 𝓝[≠] (0 : ℂ), ‖parameter‖ < step := by
    have actual : ∀ᶠ parameter in 𝓝 (0 : ℂ), parameter ∈ ball 0 step :=
      ball_mem_nhds 0 stepPositive
    simpa only [mem_ball, dist_zero_right] using actual.filter_mono nhdsWithin_le_nhds
  apply EulerNonuniqueness.General.directionalCandidate_add_of_vanishing_defect
    contourCauchyThirdDirectionalOperator data first second
    (constant := remainderConstant * (‖first‖ ^ 2 + ‖second‖ ^ 2 + ‖first + second‖ ^ 2) +
      variationConstant * ‖first‖ * ‖second‖)
  filter_upwards [smallParameters, self_mem_nhdsWithin] with parameter parameterSmall nonzero
  have parameterNonzero : parameter ≠ 0 := nonzero
  have sourceSmall : ‖parameter‖ <
      (innerRadius - ‖data - standardCircleBanach‖) / (‖first‖ + 1) :=
    parameterSmall.trans_le (min_le_left _ _)
  have shiftedNear := complexContourPerturbation_near data first near sourceSmall
  have product : ‖parameter‖ * (‖first‖ + ‖second‖ + ‖first + second‖ + 1) <
      (outerRadius - innerRadius) / 8 := by
    have parameterBound := parameterSmall.trans_le (min_le_right _ _)
    have bound := (lt_div_iff₀ (by positivity :
      0 < 8 * (‖first‖ + ‖second‖ + ‖first + second‖ + 1))).mp parameterBound
    nlinarith
  have firstNorm : ‖parameter • first‖ = ‖parameter‖ * ‖first‖ := by
    with_reducible exact norm_smul parameter first
  have secondNorm : ‖parameter • second‖ = ‖parameter‖ * ‖second‖ := by
    with_reducible exact norm_smul parameter second
  have sumNorm : ‖parameter • (first + second)‖ = ‖parameter‖ * ‖first + second‖ := by
    with_reducible exact norm_smul parameter (first + second)
  have firstSmall : ‖parameter • first‖ ≤ (outerRadius - innerRadius) / 8 := by
    rw [firstNorm]
    nlinarith [norm_nonneg parameter, norm_nonneg second, norm_nonneg (first + second)]
  have secondSmall : ‖parameter • second‖ ≤ (outerRadius - innerRadius) / 8 := by
    rw [secondNorm]
    nlinarith [norm_nonneg parameter, norm_nonneg first, norm_nonneg (first + second)]
  have sumSmall : ‖parameter • (first + second)‖ ≤ (outerRadius - innerRadius) / 8 := by
    rw [sumNorm]
    nlinarith [norm_nonneg parameter, norm_nonneg first, norm_nonneg second]
  have firstBound := contourCauchyThirdDirectionalOperator_quadratic_remainder_bound data
    (parameter • first) ((norm_nonneg _).trans near.le) gap outerSmall near.le firstSmall
  have secondBound := contourCauchyThirdDirectionalOperator_quadratic_remainder_bound
    (data + parameter • first) (parameter • second) ((norm_nonneg _).trans near.le)
    gap outerSmall shiftedNear.le secondSmall
  have sumBound := contourCauchyThirdDirectionalOperator_quadratic_remainder_bound data
    (parameter • (first + second)) ((norm_nonneg _).trans near.le) gap outerSmall near.le sumSmall
  have variation := contourCauchyThirdDirectionalOperator_difference_bound
    (data + parameter • first) data second ((norm_nonneg _).trans near.le) gap outerSmall
    shiftedNear.le near.le
  have difference : data + parameter • first - data = parameter • first := by abel
  rw [difference] at variation
  with_reducible_and_instances
    exact EulerNonuniqueness.General.directionalCandidate_additivity_defect_bound
      extendedContourCauchySecondOperatorCLM contourCauchyThirdDirectionalOperator data first second
      parameterNonzero (fun base direction => contourCauchyThirdDirectionalOperator_smul_total base direction parameter)
      (by simpa only [EulerNonuniqueness.General.directionalCandidateError, remainderConstant] using firstBound)
      (by simpa only [EulerNonuniqueness.General.directionalCandidateError, remainderConstant] using secondBound)
      (by simpa only [EulerNonuniqueness.General.directionalCandidateError, remainderConstant] using sumBound)
      (by simpa only [variationConstant] using variation)

end

end EulerNonuniqueness.Paper
