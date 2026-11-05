import Mathlib

noncomputable section

open scoped Topology ContDiff InnerProductSpace

namespace Complex

def radialRotationField (profile : ℝ → ℝ) (position : ℂ) : ℂ :=
  profile (‖position‖ ^ 2) • (I * position)

theorem fderiv_radialRotationField {profile : ℝ → ℝ} {position : ℂ}
    (differentiable : DifferentiableAt ℝ profile (‖position‖ ^ 2)) (direction : ℂ) :
    fderiv ℝ (radialRotationField profile) position direction =
      (deriv profile (‖position‖ ^ 2) * (2 * ⟪position, direction⟫_ℝ)) • (I * position) +
        profile (‖position‖ ^ 2) • (I * direction) := by
  have squared := (hasFDerivAt_id (𝕜 := ℝ) position).norm_sq
  have scalar := differentiable.hasDerivAt.comp_hasFDerivAt position squared
  have rotation := (hasFDerivAt_const (𝕜 := ℝ) I position).mul (hasFDerivAt_id (𝕜 := ℝ) position)
  have derivative := scalar.smul rotation
  simp only [Function.comp_def, id_eq] at derivative
  change fderiv ℝ (fun other : ℂ => profile (‖other‖ ^ 2) • (I * other)) position direction = _
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
    zero_mul, zero_add, mul_zero, add_zero, innerSL_apply, smul_eq_mul, _root_.id]
  rw [add_comm]
  congr 1
  simp only [two_smul, smul_eq_mul]
  ring

theorem divergence_radialRotationField {profile : ℝ → ℝ} {position : ℂ}
    (differentiable : DifferentiableAt ℝ profile (‖position‖ ^ 2)) :
    (fderiv ℝ (radialRotationField profile) position 1).re +
      (fderiv ℝ (radialRotationField profile) position I).im = 0 := by
  have innerOne : ⟪position, (1 : ℂ)⟫_ℝ = position.re := by
    rw [real_inner_eq_re_inner, RCLike.inner_apply]
    simp
  have innerImaginary : ⟪position, I⟫_ℝ = position.im := by
    rw [real_inner_eq_re_inner, RCLike.inner_apply]
    simp
  rw [fderiv_radialRotationField differentiable, fderiv_radialRotationField differentiable,
    innerOne, innerImaginary]
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
    Complex.one_im, zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub, zero_add, add_zero]
  ring

theorem contDiff_radialRotationField {profile : ℝ → ℝ} (smooth : ContDiff ℝ ∞ profile) :
    ContDiff ℝ ∞ (radialRotationField profile) := by
  have radial : ContDiff ℝ ∞ (fun position : ℂ => ‖position‖ ^ 2) := contDiff_norm_sq ℝ
  exact (smooth.comp radial).smul (contDiff_const.mul contDiff_id)

end Complex
