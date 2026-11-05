import EulerNonuniqueness.Section3.ContourStrainSourceRegularity
import EulerNonuniqueness.Section3.MovingStrainAffineResidual

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  strainSourceCoefficientDerivativeGroup strainSourceCoefficientDerivativeSpace
  centroidGaugeRegularityConstantGroup gaugeOperatorTaylorConstantSpace

theorem contourStrainSourceCoefficient_apply_actual (data : PeriodicC1HolderHalf) (coefficient : ℂ) :
    contourStrainSourceCoefficient data coefficient =
      contourCentroidGaugeProjection data (coefficient • c1Conjugate data) := by
  have actual := contourStrainSourceCoefficient_apply data coefficient
  have product : c1Product (c1Conjugate data) (c1Constant coefficient) = coefficient • c1Conjugate data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change star (data.val.1 label) * coefficient = coefficient * star (data.val.1 label)
    exact mul_comm _ _
  exact actual.trans (congrArg (contourCentroidGaugeProjection data) product)

theorem contourStrainSourceCoefficient_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      contourStrainSourceCoefficient standardCircleBanach := by
  have smooth := contourStrainSourceCoefficient_contDiffAt_three
  with_reducible_and_instances
    exact EulerNonuniqueness.General.localSecondDerivativeNear_of_contDiffAt_three smooth

theorem contourStrainSourceCoefficient_derivative_apply
    (data : PeriodicC1HolderHalf) (coefficient : ℂ)
    (regular : DifferentiableAt ℝ contourStrainSourceCoefficient data) :
    (fderiv ℝ contourStrainSourceCoefficient data).flip coefficient =
      fderiv ℝ (fun current : PeriodicC1HolderHalf =>
        contourCentroidGaugeProjection current (coefficient • c1Conjugate current)) data := by
  have evaluation : HasFDerivAt
      (fun current : PeriodicC1HolderHalf => contourStrainSourceCoefficient current coefficient)
      ((ContinuousLinearMap.apply ℝ PeriodicC1HolderHalf coefficient).comp
        (fderiv ℝ contourStrainSourceCoefficient data)) data :=
    (ContinuousLinearMap.apply ℝ PeriodicC1HolderHalf coefficient).hasFDerivAt.comp data regular.hasFDerivAt
  have equal : (fun current : PeriodicC1HolderHalf => contourStrainSourceCoefficient current coefficient) =
      (fun current => contourCentroidGaugeProjection current (coefficient • c1Conjugate current)) := by
    funext current
    exact contourStrainSourceCoefficient_apply_actual current coefficient
  rw [equal] at evaluation
  exact evaluation.fderiv.symm

end EulerNonuniqueness.Paper
