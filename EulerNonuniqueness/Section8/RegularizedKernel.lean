import EulerNonuniqueness.Definitions
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff

namespace EulerNonuniqueness

def regularizedBiotSavartKernel (scale : ℝ) (position : Plane) : Plane :=
  Complex.I * position / ((2 * Real.pi * (‖position‖ ^ 2 + scale ^ 2) : ℝ) : ℂ)

theorem regularizedBiotSavartKernel_zero (scale : ℝ) : regularizedBiotSavartKernel scale 0 = 0 := by
  simp [regularizedBiotSavartKernel]

theorem contDiff_regularizedBiotSavartKernel {scale : ℝ} (positive : 0 < scale) :
    ContDiff ℝ ∞ (regularizedBiotSavartKernel scale) := by
  have denominator : ContDiff ℝ ∞ (fun position : Plane => 2 * Real.pi * (‖position‖ ^ 2 + scale ^ 2)) :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).add contDiff_const)
  have numerator : ContDiff ℝ ∞ (fun position : Plane => Complex.I * position) := contDiff_const.mul contDiff_id
  have reciprocal := denominator.inv (fun position : Plane =>
    (mul_pos (by positivity : 0 < 2 * Real.pi) (by positivity : 0 < ‖position‖ ^ 2 + scale ^ 2)).ne')
  convert reciprocal.smul numerator using 1
  funext position
  simp only [regularizedBiotSavartKernel, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

theorem norm_regularizedBiotSavartKernel {scale : ℝ} (positive : 0 < scale) (position : Plane) :
    ‖regularizedBiotSavartKernel scale position‖ = ‖position‖ / (2 * Real.pi * (‖position‖ ^ 2 + scale ^ 2)) := by
  rw [regularizedBiotSavartKernel, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by positivity : 0 < 2 * Real.pi) (by positivity : 0 < ‖position‖ ^ 2 + scale ^ 2))]

theorem norm_regularizedBiotSavartKernel_le {scale : ℝ} (positive : 0 < scale) (position : Plane) :
    ‖regularizedBiotSavartKernel scale position‖ ≤ 1 / (2 * Real.pi * scale) := by
  rw [norm_regularizedBiotSavartKernel positive]
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.pi * (‖position‖ ^ 2 + scale ^ 2))
    (by positivity : 0 < 2 * Real.pi * scale)).mpr
  have basic : ‖position‖ * scale ≤ ‖position‖ ^ 2 + scale ^ 2 := by
    nlinarith [sq_nonneg (‖position‖ - scale), mul_nonneg (norm_nonneg position) positive.le]
  nlinarith [mul_le_mul_of_nonneg_left basic (by positivity : 0 ≤ 2 * Real.pi)]

theorem norm_regularizedBiotSavartKernel_le_kernel {scale : ℝ} (positive : 0 < scale) (position : Plane) :
    ‖regularizedBiotSavartKernel scale position‖ ≤ ‖biotSavartKernel position‖ := by
  by_cases zero : position = 0
  · simp [zero, regularizedBiotSavartKernel_zero, biotSavartKernel]
  rw [norm_regularizedBiotSavartKernel positive]
  have denominatorPositive : 0 < 2 * Real.pi * ‖position‖ ^ 2 := by positivity
  have kernelNorm : ‖biotSavartKernel position‖ = ‖position‖ / (2 * Real.pi * ‖position‖ ^ 2) := by
    rw [biotSavartKernel, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos denominatorPositive]
  rw [kernelNorm]
  exact div_le_div_of_nonneg_left (norm_nonneg _) denominatorPositive
    (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg scale]) (by positivity))

end EulerNonuniqueness
