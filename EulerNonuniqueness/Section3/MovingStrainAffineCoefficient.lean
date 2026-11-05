import EulerNonuniqueness.Section3.ContourStrainSourceActual
import EulerNonuniqueness.Section3.MovingStrainRealHigherRegularity
import EulerNonuniqueness.Section3.MovingStrainPrimitiveFormula
import EulerNonuniqueness.Section3.DiskRotatingThirdRegularity
import EulerNonuniqueness.General.AffineLinearCoefficientRegularity
import EulerNonuniqueness.General.BilinearFlipRegularity

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

local instance affineCoefficientOperatorGroup : NormedAddCommGroup
    (ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := ℂ)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

local instance affineCoefficientOperatorModule : Module ℝ
    (ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ) (M := ℂ)
    (M₃ := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₃ := RingHom.id ℝ)

local instance affineCoefficientOperatorSpace : NormedSpace ℝ
    (ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := ℂ)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def movingStrainCorrectionCoefficient (data : PeriodicC1HolderHalf) :
    ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.realifiedComplexCoefficientLift contourIndependentRealification
    contourIndependentEmbedding (independentStrainLinearCorrectionAt data)

def movingStrainPrimitiveCoefficient (data : PeriodicC1HolderHalf) : ℂ →L[ℝ] PeriodicC1HolderHalf :=
  (c1ConjugateCoefficientCLM data).comp ((ContinuousLinearMap.mul ℝ ℂ) (2 * Complex.I))

def movingStrainAffineLinearCoefficient (data : PeriodicC1HolderHalf) :
    ℂ →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.affineResidualLinearCoefficient
    (fderiv ℝ contourStrainSourceCoefficient data).flip (fderiv ℝ diskEulerRotatingField data)
    (movingStrainCorrectionCoefficient data)
    ((movingStrainCorrectionCoefficient data).comp ((ContinuousLinearMap.mul ℝ ℂ) (-Complex.I)))
    (fderiv ℝ (fderiv ℝ diskEulerRotatingField) data).flip (movingStrainPrimitiveCoefficient data)

theorem movingStrainCorrectionCoefficient_apply (data : PeriodicC1HolderHalf) (coefficient : ℂ) :
    movingStrainCorrectionCoefficient data coefficient = movingStrainRealCorrectionCLM data coefficient := by
  exact movingStrainRealCorrectionCoefficient_apply data coefficient

theorem movingStrainPrimitiveCoefficient_apply (data : PeriodicC1HolderHalf) (coefficient : ℂ) :
    movingStrainPrimitiveCoefficient data coefficient = movingStrainRealPrimitiveValue data coefficient := by
  rw [movingStrainRealPrimitiveValue_formula]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change star (data.val.1 label) * (2 * Complex.I * coefficient) =
    (2 * Complex.I * coefficient) * star (data.val.1 label)
  exact mul_comm _ _

theorem movingStrainAffineLinearCoefficient_apply (data : PeriodicC1HolderHalf)
    (coefficient : ℂ) (regular : DifferentiableAt ℝ contourStrainSourceCoefficient data) :
    movingStrainAffineLinearCoefficient data coefficient = movingStrainAffineLinearResidualCLM data coefficient := by
  have source := contourStrainSourceCoefficient_derivative_apply data coefficient regular
  have correction := movingStrainCorrectionCoefficient_apply data coefficient
  have partner := movingStrainCorrectionCoefficient_apply data (-Complex.I * coefficient)
  have primitive := movingStrainPrimitiveCoefficient_apply data coefficient
  unfold movingStrainAffineLinearCoefficient
  rw [EulerNonuniqueness.General.affineResidualLinearCoefficient_apply]
  unfold movingStrainAffineLinearResidualCLM
  with_reducible_and_instances
    simpa only [source, correction, primitive, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', partner]

end EulerNonuniqueness.Paper
