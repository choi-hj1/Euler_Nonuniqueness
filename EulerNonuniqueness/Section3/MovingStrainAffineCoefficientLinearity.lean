import EulerNonuniqueness.Section3.MovingStrainAffineCoefficient

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace
  movingStrainHigherInputsC1Group centroidGaugeRegularityConstantGroup gaugeOperatorTaylorConstantSpace
  affineCoefficientOperatorGroup affineCoefficientOperatorModule affineCoefficientOperatorSpace

def movingStrainAffineResidualCoefficient (base current : PeriodicC1HolderHalf) :
    ℂ →L[ℝ] PeriodicC1HolderHalf :=
  contourStrainSourceCoefficient current +
    (fderiv ℝ diskEulerRotatingField current).comp
      (movingStrainPrimitiveCoefficient base +
        (ContinuousLinearMap.apply ℝ PeriodicC1HolderHalf (current - base)).comp
          (movingStrainCorrectionCoefficient base)) -
    (ContinuousLinearMap.apply ℝ PeriodicC1HolderHalf (diskEulerRotatingField current)).comp
      (movingStrainCorrectionCoefficient base) -
    (movingStrainPrimitiveCoefficient base).comp ((ContinuousLinearMap.mul ℝ ℂ) (-Complex.I)) -
    (ContinuousLinearMap.apply ℝ PeriodicC1HolderHalf (current - base)).comp
      ((movingStrainCorrectionCoefficient base).comp ((ContinuousLinearMap.mul ℝ ℂ) (-Complex.I)))

theorem movingStrainAffineResidualCoefficient_apply
    (base current : PeriodicC1HolderHalf) (coefficient : ℂ) :
    movingStrainAffineResidualCoefficient base current coefficient = movingStrainAffineResidual base coefficient current := by
  unfold movingStrainAffineResidualCoefficient movingStrainAffineResidual
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.mul_apply', contourStrainSourceCoefficient_apply_actual,
    movingStrainPrimitiveCoefficient_apply, movingStrainCorrectionCoefficient_apply]

theorem movingStrainAffineResidual_sub_coefficient
    (base current : PeriodicC1HolderHalf) (first second : ℂ) :
    movingStrainAffineResidual base first current - movingStrainAffineResidual base second current =
      movingStrainAffineResidual base (first - second) current := by
  have actual := (movingStrainAffineResidualCoefficient base current).map_sub first second
  simpa only [movingStrainAffineResidualCoefficient_apply] using actual.symm

end EulerNonuniqueness.Paper
