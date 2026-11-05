import EulerNonuniqueness.General.ZeroNumeratorQuotientJet

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem zeroNumerator_nonlinearCenteredField_firstJet (head : Space → Target)
    (constant : ℂ →L[ℝ] Target) (numerator denominator : Space → ℂ) (base : Space)
    (headDifferentiable : DifferentiableAt ℝ head base)
    (numeratorDifferentiable : DifferentiableAt ℝ numerator base)
    (denominatorDifferentiable : DifferentiableAt ℝ denominator base)
    (nonzero : denominator base ≠ 0) (zeroNumerator : numerator base = 0) :
    fderiv ℝ (fun current => head current - constant (numerator current / denominator current)) base =
      fderiv ℝ (fun current => head current - constant (numerator current / denominator base)) base := by
  have variableRatio := zeroNumeratorQuotient_hasFDerivAt numerator denominator base
    numeratorDifferentiable denominatorDifferentiable nonzero zeroNumerator
  have fixedRatio : HasFDerivAt (fun current => numerator current / denominator base)
      ((denominator base)⁻¹ • fderiv ℝ numerator base) base := by
    simpa only [div_eq_mul_inv] using numeratorDifferentiable.hasFDerivAt.mul_const (denominator base)⁻¹
  have variableJet := headDifferentiable.hasFDerivAt.sub (constant.hasFDerivAt.comp base variableRatio)
  have fixedJet := headDifferentiable.hasFDerivAt.sub (constant.hasFDerivAt.comp base fixedRatio)
  exact variableJet.fderiv.trans fixedJet.fderiv.symm

end

end EulerNonuniqueness.General
