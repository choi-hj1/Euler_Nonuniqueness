import EulerNonuniqueness.Section3.ProjectedForcingRealEquation
import EulerNonuniqueness.Section3.IndependentForcingRealOperator

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace
  realCorrectionOperatorC1Group realCorrectionOperatorC1Semi realCorrectionRealOperatorGroup

def projectedForcingRealCorrectionCLM (degree : ℕ) (coefficient : ℂ) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (independentForcingRealCorrectionCLM degree coefficient).comp
    (contourCentroidGaugeProjection standardCircleBanach)

theorem projectedForcingRealCorrectionCLM_apply (degree : ℕ) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) :
    projectedForcingRealCorrectionCLM degree coefficient direction =
      contourIndependentRealification
        (coefficient • projectedIndependentForcingLinearCorrection degree direction) := by
  rw [projectedForcingRealCorrectionCLM, ContinuousLinearMap.comp_apply,
    independentForcingRealCorrectionCLM_apply, projectedIndependentForcingLinearCorrection]

theorem projectedForcingRealCorrectionCLM_norm_le (degree : ℕ) (coefficient : ℂ) :
    ‖projectedForcingRealCorrectionCLM degree coefficient‖ ≤
      (2 * ‖coefficient‖ * ‖independentForcingLinearCorrection degree‖) *
        ‖contourCentroidGaugeProjection standardCircleBanach‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (independentForcingRealCorrectionCLM_norm_le degree coefficient)
    (norm_nonneg _)

theorem projectedForcingRealCorrectionCLM_actual_equation (degree : ℕ) (coefficient : ℂ)
    (direction : PeriodicC1HolderHalf) (member : direction ∈ contourContinuousVectorSubmodule) :
    (((degree + 2 : ℕ) : ℝ) / 2) •
        projectedForcingRealCorrectionCLM degree (-Complex.I * coefficient) direction +
      projectedForcingRealCorrectionCLM degree coefficient (diskRotatingDerivative direction) -
      diskRotatingDerivative (projectedForcingRealCorrectionCLM degree coefficient direction) =
      fderiv ℝ (fun data : PeriodicC1HolderHalf => contourCentroidGaugeProjection data
        (coefficient • c1Conjugate (c1NaturalPower data (degree + 1)))) standardCircleBanach
        (contourCentroidGaugeProjection standardCircleBanach direction) +
      fderiv ℝ (fderiv ℝ diskEulerRotatingField) standardCircleBanach
        (contourCentroidGaugeProjection standardCircleBanach direction)
        (contourIndependentRealification (coefficient • independentForcingPrimitiveValue degree)) := by
  simp only [projectedForcingRealCorrectionCLM_apply]
  have equation := projectedForcing_actual_real_homological_equation degree coefficient direction member
  rw [contourIndependentRealification_frequency] at equation
  exact equation

end

end EulerNonuniqueness.Paper
