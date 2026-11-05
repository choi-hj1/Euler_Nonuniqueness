import EulerNonuniqueness.Section3.MovingStrainRealCorrection
import EulerNonuniqueness.General.RealifiedCoefficientDerivative
import EulerNonuniqueness.Section3.DiskForcingPrimitive

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group independentRealificationOutputGroup
  independentRealificationInputGroup forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

theorem movingStrainRealPrimitiveValue_hasDerivAt (data : PeriodicC1HolderHalf)
    {coefficient : ℝ → ℂ} {slope : ℂ} {time : ℝ} (derivative : HasDerivAt coefficient slope time) :
    HasDerivAt (fun current => movingStrainRealPrimitiveValue data (coefficient current))
      (movingStrainRealPrimitiveValue data slope) time := by
  unfold movingStrainRealPrimitiveValue
  with_reducible_and_instances
    exact EulerNonuniqueness.General.realifiedCoefficient_hasDerivAt contourIndependentRealification
      (independentStrainPrimitiveAt data) derivative

theorem movingStrainRealCorrectionCLM_hasDerivAt (data : PeriodicC1HolderHalf)
    {coefficient : ℝ → ℂ} {slope : ℂ} {time : ℝ} (derivative : HasDerivAt coefficient slope time) :
    HasDerivAt (fun current => movingStrainRealCorrectionCLM data (coefficient current))
      (movingStrainRealCorrectionCLM data slope) time := by
  unfold movingStrainRealCorrectionCLM
  with_reducible_and_instances
    exact EulerNonuniqueness.General.realifiedOperatorCoefficient_hasDerivAt contourIndependentRealification
      contourIndependentEmbedding (independentStrainLinearCorrectionAt data) derivative

theorem movingStrainRealCorrectionCLM_add (data : PeriodicC1HolderHalf) (first second : ℂ) :
    movingStrainRealCorrectionCLM data (first + second) =
      movingStrainRealCorrectionCLM data first + movingStrainRealCorrectionCLM data second := by
  unfold movingStrainRealCorrectionCLM
  with_reducible_and_instances
    simpa only [EulerNonuniqueness.General.realifiedOperatorCoefficientCLM_apply] using
      (EulerNonuniqueness.General.realifiedOperatorCoefficientCLM contourIndependentRealification
        contourIndependentEmbedding (independentStrainLinearCorrectionAt data)).map_add first second

theorem movingStrainRealCorrectionCLM_real_smul (data : PeriodicC1HolderHalf) (scalar : ℝ) (coefficient : ℂ) :
    movingStrainRealCorrectionCLM data (scalar • coefficient) =
      scalar • movingStrainRealCorrectionCLM data coefficient := by
  unfold movingStrainRealCorrectionCLM
  with_reducible_and_instances
    simpa only [EulerNonuniqueness.General.realifiedOperatorCoefficientCLM_apply] using
      (EulerNonuniqueness.General.realifiedOperatorCoefficientCLM contourIndependentRealification
        contourIndependentEmbedding (independentStrainLinearCorrectionAt data)).map_smul scalar coefficient

theorem movingStrainRealPrimitiveValue_add (data : PeriodicC1HolderHalf) (first second : ℂ) :
    movingStrainRealPrimitiveValue data (first + second) =
      movingStrainRealPrimitiveValue data first + movingStrainRealPrimitiveValue data second := by
  unfold movingStrainRealPrimitiveValue
  rw [add_smul, map_add]

theorem movingStrainRealPrimitiveValue_real_smul (data : PeriodicC1HolderHalf) (scalar : ℝ) (coefficient : ℂ) :
    movingStrainRealPrimitiveValue data (scalar • coefficient) =
      scalar • movingStrainRealPrimitiveValue data coefficient := by
  unfold movingStrainRealPrimitiveValue
  rw [smul_assoc, map_smul]

theorem diskStrainModulatedCoefficient_hasDerivAt (frequency time : ℝ)
    {amplitude : ℝ → ℂ} {slope : ℂ} (derivative : HasDerivAt amplitude slope time) :
    HasDerivAt (fun current => diskForcingPhase 0 frequency current * amplitude current)
      ((frequency : ℂ) * (-Complex.I * (diskForcingPhase 0 frequency time * amplitude time)) +
        diskForcingPhase 0 frequency time * slope) time := by
  convert (diskForcingPhase_hasDerivAt 0 frequency time).mul derivative using 1
  norm_num
  ring

end EulerNonuniqueness.Paper
