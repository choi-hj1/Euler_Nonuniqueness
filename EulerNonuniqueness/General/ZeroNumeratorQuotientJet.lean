import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem zeroNumeratorQuotient_hasFDerivAt (numerator denominator : Space → ℂ) (base : Space)
    (numeratorDifferentiable : DifferentiableAt ℝ numerator base)
    (denominatorDifferentiable : DifferentiableAt ℝ denominator base)
    (nonzero : denominator base ≠ 0) (zeroNumerator : numerator base = 0) :
    HasFDerivAt (fun current => numerator current / denominator current)
      ((denominator base)⁻¹ • fderiv ℝ numerator base) base := by
  have inverseJet := (denominatorDifferentiable.inv nonzero).hasFDerivAt
  have productJet := numeratorDifferentiable.hasFDerivAt.mul inverseJet
  have cleanJet : HasFDerivAt (fun current => numerator current * (denominator current)⁻¹)
      ((denominator base)⁻¹ • fderiv ℝ numerator base) base := by
    apply productJet.congr_fderiv
    apply ContinuousLinearMap.ext
    intro vector
    change numerator base * (fderiv ℝ (fun current => (denominator current)⁻¹) base vector) +
      (denominator base)⁻¹ * (fderiv ℝ numerator base vector) =
      (denominator base)⁻¹ * (fderiv ℝ numerator base vector)
    rw [zeroNumerator, zero_mul, zero_add]
  simpa only [div_eq_mul_inv] using cleanJet

end

end EulerNonuniqueness.General
