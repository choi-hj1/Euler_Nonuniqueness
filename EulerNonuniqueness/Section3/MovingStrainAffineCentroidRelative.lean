import EulerNonuniqueness.Section3.MovingStrainAffineLinearUniform
import EulerNonuniqueness.Section3.MovingStrainCentroidDefect
import EulerNonuniqueness.General.AffineResidualRelativeRemainder
import EulerNonuniqueness.General.LinearQuadraticConstraintRelative

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem movingStrainAffineLinearResidualCLM_exists_relative_constraint_ball :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ initialAngular finalAngular : PeriodicC1HolderHalf,
      ∀ (initialSmall : ‖initialAngular‖ < 1 / 2) (finalSmall : ‖finalAngular‖ < 1 / 2),
      initialAngular ∈ contourContinuousVectorSubmodule → finalAngular ∈ contourContinuousVectorSubmodule →
      let initialBase := fixedRelabelEquivalence initialAngular initialSmall standardCircleBanach
      let finalBase := fixedRelabelEquivalence finalAngular finalSmall standardCircleBanach
      ‖initialBase - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) →
      ‖finalBase - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) →
      ∀ initialIncrement finalIncrement : PeriodicC1HolderHalf,
      initialIncrement ∈ contourContinuousVectorSubmodule → finalIncrement ∈ contourContinuousVectorSubmodule →
      ‖initialBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      contourCentroidFunctional (initialBase + initialIncrement) = contourCentroidFunctional initialBase →
      contourCentroidFunctional (finalBase + finalIncrement) = contourCentroidFunctional finalBase →
      ∀ coefficient : ℂ,
      ‖movingStrainAffineLinearResidualCLM initialBase coefficient initialIncrement -
        movingStrainAffineLinearResidualCLM finalBase coefficient finalIncrement‖ ≤
      constant * ‖coefficient‖ *
        ((‖initialIncrement‖ + ‖finalIncrement‖) * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * (‖initialIncrement‖ + ‖finalIncrement‖) ^ 2) := by
  obtain ⟨linearRadius, linearPositive, linearConstant, linearOne, linearAbsolute, linearDifference⟩ :=
    movingStrainAffineLinearResidualCLM_exists_uniform_base_bounds
  obtain ⟨centroidRadius, centroidPositive, centroidConstant, centroidDifference⟩ :=
    contourCentroidDerivative_exists_relative_quadratic_constraint_ball
  refine ⟨min linearRadius centroidRadius, lt_min linearPositive centroidPositive,
    2 * linearConstant * centroidConstant, by positivity, ?_⟩
  intro initialAngular finalAngular initialSmall finalSmall initialMember finalMember initialBase finalBase
    initialNearby finalNearby initialIncrement finalIncrement initialIncrementMember finalIncrementMember
    initialInside finalInside initialCentroid finalCentroid coefficient
  have initialRadius : ‖initialBase - standardCircleBanach‖ ≤ linearRadius := by
    have bound := initialInside.trans (min_le_left linearRadius centroidRadius)
    linarith [norm_nonneg initialIncrement, norm_nonneg finalIncrement]
  have finalRadius : ‖finalBase - standardCircleBanach‖ ≤ linearRadius := by
    have bound := finalInside.trans (min_le_left linearRadius centroidRadius)
    linarith [norm_nonneg initialIncrement, norm_nonneg finalIncrement]
  have initialConstraint := initialInside.trans (min_le_right linearRadius centroidRadius)
  have finalConstraint := finalInside.trans (min_le_right linearRadius centroidRadius)
  have centroidRelative := centroidDifference initialBase finalBase initialIncrement finalIncrement
    initialConstraint finalConstraint initialCentroid finalCentroid
  have finalSingle : ‖finalBase - standardCircleBanach‖ + (‖finalIncrement‖ + ‖(0 : PeriodicC1HolderHalf)‖) ≤
      centroidRadius := by
    simp only [norm_zero, add_zero]
    linarith [norm_nonneg initialIncrement]
  have centroidAbsolute := centroidDifference finalBase finalBase finalIncrement 0 finalSingle finalSingle
    finalCentroid (by simp only [add_zero])
  simp only [map_zero, sub_zero, sub_self, norm_zero, mul_zero, zero_mul, add_zero] at centroidAbsolute
  have firstFactor := movingStrainAffineLinearResidualCLM_eq_centroid_defect
    initialAngular initialSmall initialMember initialNearby coefficient initialIncrement initialIncrementMember
  have secondFactor := movingStrainAffineLinearResidualCLM_eq_centroid_defect
    finalAngular finalSmall finalMember finalNearby coefficient finalIncrement finalIncrementMember
  rw [firstFactor, secondFactor]
  let firstValue := fderiv ℝ contourCentroidFunctional initialBase initialIncrement
  let secondValue := fderiv ℝ contourCentroidFunctional finalBase finalIncrement
  have constantDifference : ‖c1Constant firstValue - c1Constant secondValue‖ ≤ ‖firstValue - secondValue‖ := by
    have equality : c1Constant firstValue - c1Constant secondValue = c1Constant (firstValue - secondValue) := by
      exact (c1ConstantCLM.map_sub firstValue secondValue).symm
    rw [equality]
    exact c1Constant_norm_bound _
  have vectorRelative := constantDifference.trans centroidRelative
  have vectorAbsolute : ‖c1Constant secondValue‖ ≤ (centroidConstant : ℝ) * ‖finalIncrement‖ ^ 2 := by
    simpa only [pow_two] using (c1Constant_norm_bound secondValue).trans centroidAbsolute
  have firstLinear := linearAbsolute initialBase initialRadius coefficient
  have differenceLinear := linearDifference initialBase finalBase initialRadius finalRadius coefficient
  have finalNorm : ‖finalIncrement‖ ≤ ‖initialIncrement‖ + ‖finalIncrement‖ := by
    linarith [norm_nonneg initialIncrement]
  have linearNonnegative : 0 ≤ linearConstant := by linarith
  with_reducible_and_instances
    exact EulerNonuniqueness.General.norm_linear_quadratic_constraint_difference_le
      (Space := PeriodicC1HolderHalf)
      (movingStrainAffineLinearResidualCLM initialBase coefficient)
      (movingStrainAffineLinearResidualCLM finalBase coefficient) (c1Constant firstValue) (c1Constant secondValue)
      linearNonnegative centroidConstant.coe_nonneg (norm_nonneg coefficient)
      (add_nonneg (norm_nonneg initialIncrement) (norm_nonneg finalIncrement))
      (norm_nonneg (initialIncrement - finalIncrement)) (norm_nonneg (initialBase - finalBase))
      (norm_nonneg finalIncrement) finalNorm firstLinear differenceLinear vectorRelative vectorAbsolute

end EulerNonuniqueness.Paper
