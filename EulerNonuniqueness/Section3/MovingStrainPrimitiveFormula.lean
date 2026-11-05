import EulerNonuniqueness.Section3.MovingStrainRealCorrection
import EulerNonuniqueness.Section3.RelabeledDiskForcingPrimitive

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem movingStrainRealPrimitiveValue_formula (data : PeriodicC1HolderHalf) (coefficient : ℂ) :
    movingStrainRealPrimitiveValue data coefficient =
      (2 * Complex.I * coefficient) • c1Conjugate data := by
  unfold movingStrainRealPrimitiveValue independentStrainPrimitiveAt
  change contourIndependentRealification
    (coefficient • (diskForcingPrimitiveFactor 0 1 • c1Conjugate data), coefficient • (0 : PeriodicC1HolderHalf)) = _
  rw [smul_zero, contourIndependentRealification_positive, smul_smul]
  congr 1
  norm_num [diskForcingPrimitiveFactor]
  ring

theorem movingStrainRealPrimitiveValue_norm_bound (data : PeriodicC1HolderHalf) (coefficient : ℂ) :
    ‖movingStrainRealPrimitiveValue data coefficient‖ ≤ 2 * ‖coefficient‖ * ‖data‖ := by
  rw [movingStrainRealPrimitiveValue_formula, norm_smul, norm_mul, norm_mul]
  norm_num
  exact mul_le_mul_of_nonneg_left (c1Conjugate_norm_bound data) (by positivity)

theorem movingStrainRealPrimitiveValue_difference_bound (first second : PeriodicC1HolderHalf)
    (coefficient : ℂ) :
    ‖movingStrainRealPrimitiveValue first coefficient - movingStrainRealPrimitiveValue second coefficient‖ ≤
      2 * ‖coefficient‖ * ‖first - second‖ := by
  rw [movingStrainRealPrimitiveValue_formula, movingStrainRealPrimitiveValue_formula, ← smul_sub,
    norm_smul, norm_mul, norm_mul]
  norm_num
  exact mul_le_mul_of_nonneg_left (c1Conjugate_difference_norm_bound first second) (by positivity)

end EulerNonuniqueness.Paper
