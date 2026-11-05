import EulerNonuniqueness.Section3.IndependentForcingSpectralSolver
import EulerNonuniqueness.General.HalfIntegerDenominator

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentDenominatorC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def independentDiskSpectralInteger (branch : Fin 3) : ℤ := ![0, 1, -1] branch

theorem independentDiskSpectralEigenvalue_integer (branch : Fin 3) :
    independentDiskSpectralEigenvalue branch = Complex.I * (independentDiskSpectralInteger branch : ℂ) / 2 := by
  fin_cases branch <;> norm_num [independentDiskSpectralEigenvalue,
    EulerNonuniqueness.General.complexCubicEigenvalue, independentDiskSpectralInteger,
    Matrix.cons_val_zero', Matrix.cons_val_succ']

theorem independentForcingDenominator_integer (degree : ℕ) (output input : Fin 3) :
    -Complex.I * ((degree + 2 : ℕ) : ℂ) / 2 + independentDiskSpectralEigenvalue input -
      independentDiskSpectralEigenvalue output = Complex.I *
      ((independentDiskSpectralInteger input - independentDiskSpectralInteger output - (degree + 2) : ℤ) : ℂ) / 2 := by
  rw [independentDiskSpectralEigenvalue_integer, independentDiskSpectralEigenvalue_integer]
  push_cast
  ring

theorem independentForcingDenominator_inverse_norm_le (degree : ℕ) (output input : Fin 3) :
    ‖(-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2 + independentDiskSpectralEigenvalue input -
      independentDiskSpectralEigenvalue output)⁻¹‖ ≤ 2 := by
  rw [independentForcingDenominator_integer]
  exact EulerNonuniqueness.General.halfIntegerImaginary_inverse_norm_le _

theorem independentForcingDenominator_zero_iff (degree : ℕ) (output input : Fin 3) :
    -Complex.I * ((degree + 2 : ℕ) : ℂ) / 2 + independentDiskSpectralEigenvalue input -
      independentDiskSpectralEigenvalue output = 0 ↔ degree = 0 ∧ output = 2 ∧ input = 1 := by
  rw [independentForcingDenominator_integer]
  have scalarZero (integer : ℤ) : Complex.I * (integer : ℂ) / 2 = 0 ↔ integer = 0 := by
    simp only [div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, mul_eq_zero, Complex.I_ne_zero,
      false_or, Int.cast_eq_zero]
  rw [scalarZero]
  fin_cases output <;> fin_cases input <;>
    norm_num [independentDiskSpectralInteger, Matrix.cons_val_zero', Matrix.cons_val_succ', Fin.ext_iff] <;> omega

theorem independentForcingLinearCorrection_uniform_norm_le (degree : ℕ) :
    ‖independentForcingLinearCorrection degree‖ ≤
      2 * (∑ branch : Fin 3, ‖independentDiskSpectralProjection branch‖) ^ 2 *
        ‖independentForcingLinearCoefficient degree‖ := by
  unfold independentForcingLinearCorrection
  with_reducible
    exact EulerNonuniqueness.General.finiteSpectralHomologicalSolver_norm_le_uniform
      independentDiskSpectralProjection independentDiskSpectralEigenvalue
      (-Complex.I * ((degree + 2 : ℕ) : ℂ) / 2) (independentForcingLinearCoefficient degree)
      (independentForcingDenominator_inverse_norm_le degree)

end

end EulerNonuniqueness.Paper
