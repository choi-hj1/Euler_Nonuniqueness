import EulerNonuniqueness.Section8.RegularizedKernelDerivative

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem real_inner_complex_one (position : Plane) : ⟪position, (1 : Plane)⟫_ℝ = position.re := by
  rw [real_inner_eq_re_inner, RCLike.inner_apply]
  change ((1 : ℂ) * (starRingEnd ℂ) position).re = position.re
  simp

theorem real_inner_complex_I (position : Plane) : ⟪position, Complex.I⟫_ℝ = position.im := by
  rw [real_inner_eq_re_inner, RCLike.inner_apply]
  change (Complex.I * (starRingEnd ℂ) position).re = position.im
  simp

theorem divergence_regularizedBiotSavartKernel {scale : ℝ} (positive : 0 < scale) (position : Plane) :
    (fderiv ℝ (regularizedBiotSavartKernel scale) position 1).re +
      (fderiv ℝ (regularizedBiotSavartKernel scale) position Complex.I).im = 0 := by
  rw [fderiv_regularizedBiotSavartKernel positive, fderiv_regularizedBiotSavartKernel positive]
  simp only [real_inner_complex_one, real_inner_complex_I, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im, zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub, zero_add, add_zero]
  ring

end EulerNonuniqueness
