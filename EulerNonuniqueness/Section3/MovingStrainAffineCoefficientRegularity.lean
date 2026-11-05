import EulerNonuniqueness.Section3.MovingStrainAffineCoefficient

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace
  movingStrainPairBilinearGroup movingStrainPairBilinearSpace
  movingNumeratorRealOperatorSpace movingNumeratorRealBilinearSpace
  movingNumeratorInnerSpace movingNumeratorTupleSpace movingStrainHigherInputsC1Group
  strainSourceCoefficientDerivativeGroup strainSourceCoefficientDerivativeSpace
  centroidGaugeRegularityConstantGroup gaugeOperatorTaylorConstantSpace
  affineCoefficientOperatorGroup affineCoefficientOperatorModule affineCoefficientOperatorSpace

theorem movingStrainCorrectionCoefficient_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      movingStrainCorrectionCoefficient standardCircleBanach := by
  have regular := movingStrainRealCorrectionCoefficient_hasLipschitzDerivativeNear
  unfold movingStrainCorrectionCoefficient
  with_reducible_and_instances exact regular

theorem movingStrainPrimitiveCoefficient_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      movingStrainPrimitiveCoefficient standardCircleBanach := by
  have conjugate : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun data : PeriodicC1HolderHalf => c1ConjugateCoefficientCLM data) standardCircleBanach := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap
        (Space := PeriodicC1HolderHalf) (Target := ℂ →L[ℝ] PeriodicC1HolderHalf)
        c1ConjugateCoefficientCLM standardCircleBanach
  have multiplier : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun _ : PeriodicC1HolderHalf => (ContinuousLinearMap.mul ℝ ℂ) (2 * Complex.I)) standardCircleBanach :=
    EulerNonuniqueness.General.hasLipschitzDerivativeNear_const _ _
  unfold movingStrainPrimitiveCoefficient
  have combined := EulerNonuniqueness.General.HasLipschitzDerivativeNear.bilinear
      (Space := PeriodicC1HolderHalf) (Middle := ℂ →L[ℝ] PeriodicC1HolderHalf)
      (Target := ℂ →L[ℝ] ℂ) (Range := ℂ →L[ℝ] PeriodicC1HolderHalf)
      (ContinuousLinearMap.compL ℝ ℂ ℂ PeriodicC1HolderHalf) conjugate multiplier
  simpa only [ContinuousLinearMap.compL_apply] using combined

theorem movingStrainAffineLinearCoefficient_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      movingStrainAffineLinearCoefficient standardCircleBanach := by
  have source := contourStrainSourceCoefficient_hasLipschitzSecondDerivativeNear.2
  have sourceFlipped := source.flip
  have generator := diskEulerRotatingField_derivative_hasLipschitzDerivativeNear
  have correction := movingStrainCorrectionCoefficient_hasLipschitzDerivativeNear
  have primitive := movingStrainPrimitiveCoefficient_hasLipschitzDerivativeNear
  have second := diskEulerRotatingField_derivative_hasLipschitzSecondDerivativeNear.2
  have secondFlipped := second.flip
  let sourceField : PeriodicC1HolderHalf → ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fun data => (fderiv ℝ contourStrainSourceCoefficient data).flip
  let generatorField : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskEulerRotatingField
  let secondField : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fun data => (fderiv ℝ (fderiv ℝ diskEulerRotatingField) data).flip
  have multiplier : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun _ : PeriodicC1HolderHalf => (ContinuousLinearMap.mul ℝ ℂ) (-Complex.I)) standardCircleBanach :=
    EulerNonuniqueness.General.hasLipschitzDerivativeNear_const _ _
  have partner : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun data => (movingStrainCorrectionCoefficient data).comp
        ((ContinuousLinearMap.mul ℝ ℂ) (-Complex.I))) standardCircleBanach := by
    have combined := EulerNonuniqueness.General.HasLipschitzDerivativeNear.bilinear
        (Space := PeriodicC1HolderHalf) (Middle := ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
        (Target := ℂ →L[ℝ] ℂ) (Range := ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
        (ContinuousLinearMap.compL ℝ ℂ ℂ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)) correction multiplier
    simpa only [ContinuousLinearMap.compL_apply] using combined
  unfold movingStrainAffineLinearCoefficient
  with_reducible_and_instances
    exact EulerNonuniqueness.General.affineResidualLinearCoefficient_hasLipschitzDerivativeNear
      sourceField generatorField movingStrainCorrectionCoefficient
      (fun data => (movingStrainCorrectionCoefficient data).comp ((ContinuousLinearMap.mul ℝ ℂ) (-Complex.I)))
      secondField
      movingStrainPrimitiveCoefficient standardCircleBanach sourceFlipped generator correction partner secondFlipped primitive

end EulerNonuniqueness.Paper
