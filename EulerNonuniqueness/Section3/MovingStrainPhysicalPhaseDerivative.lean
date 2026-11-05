import EulerNonuniqueness.Section3.MovingStrainRealCoefficientDerivative

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem movingStrainPhysicalPrimitive_hasDerivAt (data : PeriodicC1HolderHalf)
    {frequency time : ℝ} (nonzero : frequency ≠ 0) {amplitude : ℝ → ℂ} {slope : ℂ}
    (derivative : HasDerivAt amplitude slope time) :
    HasDerivAt (fun current => frequency⁻¹ • movingStrainRealPrimitiveValue data
      (diskForcingPhase 0 frequency current * amplitude current))
      (movingStrainRealPrimitiveValue data (-Complex.I * (diskForcingPhase 0 frequency time * amplitude time)) +
        frequency⁻¹ • movingStrainRealPrimitiveValue data (diskForcingPhase 0 frequency time * slope)) time := by
  have actual := (movingStrainRealPrimitiveValue_hasDerivAt data
    (diskStrainModulatedCoefficient_hasDerivAt frequency time derivative)).const_smul frequency⁻¹
  have cast (value : ℂ) : (frequency : ℂ) * value = frequency • value := rfl
  rw [cast, movingStrainRealPrimitiveValue_add, movingStrainRealPrimitiveValue_real_smul,
    smul_add, smul_smul, inv_mul_cancel₀ nonzero, one_smul] at actual
  exact actual

theorem movingStrainPhysicalCorrection_hasDerivAt (data : PeriodicC1HolderHalf)
    {frequency time : ℝ} (nonzero : frequency ≠ 0) {amplitude : ℝ → ℂ} {slope : ℂ}
    (derivative : HasDerivAt amplitude slope time) :
    HasDerivAt (fun current => frequency⁻¹ • movingStrainRealCorrectionCLM data
      (diskForcingPhase 0 frequency current * amplitude current))
      (movingStrainRealCorrectionCLM data (-Complex.I * (diskForcingPhase 0 frequency time * amplitude time)) +
        frequency⁻¹ • movingStrainRealCorrectionCLM data (diskForcingPhase 0 frequency time * slope)) time := by
  have actual := (movingStrainRealCorrectionCLM_hasDerivAt data
    (diskStrainModulatedCoefficient_hasDerivAt frequency time derivative)).const_smul frequency⁻¹
  have cast (value : ℂ) : (frequency : ℂ) * value = frequency • value := rfl
  rw [cast, movingStrainRealCorrectionCLM_add, movingStrainRealCorrectionCLM_real_smul,
    smul_add, smul_smul, inv_mul_cancel₀ nonzero, one_smul] at actual
  exact actual

end EulerNonuniqueness.Paper
