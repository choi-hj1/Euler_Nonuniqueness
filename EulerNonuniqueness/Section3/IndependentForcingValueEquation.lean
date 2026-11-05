import EulerNonuniqueness.Section3.IndependentForcingLinearCoefficient
import EulerNonuniqueness.General.ComplexPairEigenplane

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentValueEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def independentDiskRotatingDerivative :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexPairExtension c1ConjugateCLM c1ConjugateCLM_complex_smul diskRotatingDerivative

theorem independentDiskRotatingDerivative_forcing_mode (degree : ℕ) (coefficient : ℂ) :
    independentDiskRotatingDerivative (coefficient • c1Conjugate (diskCircleMode (degree + 1)), 0) =
      (-Complex.I / 2) • (coefficient • c1Conjugate (diskCircleMode (degree + 1)), 0) := by
  have imaginary : diskRotatingDerivative (Complex.I • (coefficient • c1Conjugate (diskCircleMode (degree + 1)))) =
      Complex.I • diskRotatingDerivative (coefficient • c1Conjugate (diskCircleMode (degree + 1))) := by
    rw [smul_smul, diskRotatingDerivative_forcing_mode, diskRotatingDerivative_forcing_mode, smul_smul]
    congr 1
    ring
  have result := EulerNonuniqueness.General.complexPairExtension_positive_eigenplane c1ConjugateCLM
    c1ConjugateCLM_complex_smul c1ConjugateCLM_involution diskRotatingDerivative
    (coefficient • c1Conjugate (diskCircleMode (degree + 1))) imaginary
  change independentDiskRotatingDerivative (coefficient • c1Conjugate (diskCircleMode (degree + 1)), 0) = _ at result
  rw [result, diskRotatingDerivative_forcing_mode]
  apply Prod.ext
  · change (-Complex.I / 2 * coefficient) • _ = (-Complex.I / 2) • (coefficient • _)
    rw [smul_smul]
  · simp only [Prod.smul_snd, smul_zero]

theorem independentForcingPrimitiveValue_equation (degree : ℕ) :
    (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) • independentForcingPrimitiveValue degree -
      independentDiskRotatingDerivative (independentForcingPrimitiveValue degree) =
      (c1Conjugate (diskCircleMode (degree + 1)), 0) := by
  have scalar := diskForcingPrimitiveFactor_identity degree (frequency := 1) (by norm_num)
  simp only [Complex.ofReal_one, mul_one, one_mul] at scalar
  unfold independentForcingPrimitiveValue
  rw [independentDiskRotatingDerivative_forcing_mode]
  apply Prod.ext
  · apply PeriodicC1HolderHalf.ext_value
    intro label
    change (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) * (diskForcingPrimitiveFactor degree 1 * _) -
      (-Complex.I / 2) * (diskForcingPrimitiveFactor degree 1 * _) = _
    linear_combination ((c1Conjugate (diskCircleMode (degree + 1))).val.1 label) * scalar
  · simp

end

end EulerNonuniqueness.Paper
