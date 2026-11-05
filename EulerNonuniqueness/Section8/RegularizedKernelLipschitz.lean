import EulerNonuniqueness.Section8.RegularizedKernelDerivative
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem norm_fderiv_regularizedBiotSavartKernel_le {scale : ℝ} (positive : 0 < scale) (position direction : Plane) :
    ‖fderiv ℝ (regularizedBiotSavartKernel scale) position direction‖ ≤
      (3 / (2 * Real.pi * scale ^ 2)) * ‖direction‖ := by
  let denominator := 2 * Real.pi * (‖position‖ ^ 2 + scale ^ 2)
  have denominatorPositive : 0 < denominator := by dsimp [denominator]; positivity
  have factorPositive : 0 < 2 * Real.pi := by positivity
  have radialBound : 2 * Real.pi * ‖position‖ ^ 2 ≤ denominator := by
    dsimp [denominator]
    nlinarith [mul_nonneg factorPositive.le (sq_nonneg scale)]
  have radialRatio : 2 * Real.pi * ‖position‖ ^ 2 * denominator⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one denominatorPositive]
    exact radialBound
  have innerBound : |⟪position, direction⟫_ℝ| ≤ ‖position‖ * ‖direction‖ := by
    simpa only [Real.norm_eq_abs] using (@norm_inner_le_norm ℝ Plane _ _ _ position direction)
  have rawBound : ‖fderiv ℝ (regularizedBiotSavartKernel scale) position direction‖ ≤
      denominator⁻¹ * ‖direction‖ + (denominator ^ 2)⁻¹ *
        (2 * Real.pi * (2 * (‖position‖ * ‖direction‖))) * ‖position‖ := by
    rw [fderiv_regularizedBiotSavartKernel positive]
    apply (norm_add_le _ _).trans
    simp only [norm_smul, norm_mul, norm_neg, norm_inv, norm_pow, Real.norm_eq_abs,
      abs_of_pos denominatorPositive, Complex.norm_I, one_mul, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by positivity : 0 < ‖position‖ ^ 2 + scale ^ 2)]
    change denominator⁻¹ * ‖direction‖ + (denominator ^ 2)⁻¹ *
      (2 * Real.pi * (2 * |⟪position, direction⟫_ℝ|)) * ‖position‖ ≤ _
    gcongr
  have secondBound : (denominator ^ 2)⁻¹ * (2 * Real.pi * (2 * (‖position‖ * ‖direction‖))) * ‖position‖ ≤
      2 * denominator⁻¹ * ‖direction‖ := by
    calc
      _ = 2 * (2 * Real.pi * ‖position‖ ^ 2 * denominator⁻¹) * (denominator⁻¹ * ‖direction‖) := by
        rw [← inv_pow]
        ring
      _ ≤ 2 * 1 * (denominator⁻¹ * ‖direction‖) := by gcongr
      _ = _ := by ring
  have coefficientBound : 3 * denominator⁻¹ ≤ 3 / (2 * Real.pi * scale ^ 2) := by
    rw [← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    dsimp [denominator]
    nlinarith [mul_nonneg factorPositive.le (sq_nonneg ‖position‖)]
  calc
    _ ≤ denominator⁻¹ * ‖direction‖ + (denominator ^ 2)⁻¹ * (2 * Real.pi * (2 * (‖position‖ * ‖direction‖))) * ‖position‖ := rawBound
    _ ≤ denominator⁻¹ * ‖direction‖ + 2 * denominator⁻¹ * ‖direction‖ := add_le_add_left secondBound _
    _ = (3 * denominator⁻¹) * ‖direction‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right coefficientBound (norm_nonneg _)

theorem lipschitz_regularizedBiotSavartKernel {scale : ℝ} (positive : 0 < scale) :
    LipschitzWith ⟨3 / (2 * Real.pi * scale ^ 2), by positivity⟩ (regularizedBiotSavartKernel scale) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((contDiff_regularizedBiotSavartKernel positive).differentiable (by simp))
  intro position
  change ‖fderiv ℝ (regularizedBiotSavartKernel scale) position‖ ≤ 3 / (2 * Real.pi * scale ^ 2)
  exact (fderiv ℝ (regularizedBiotSavartKernel scale) position).opNorm_le_bound (by positivity)
    (norm_fderiv_regularizedBiotSavartKernel_le positive position)

end EulerNonuniqueness
