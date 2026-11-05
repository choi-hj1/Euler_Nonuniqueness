import EulerNonuniqueness.Section6.MovingPatchDerivative
import Mathlib.Analysis.Complex.OperatorNorm

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem inverse_square_difference_bound {first second : ℂ} {distance : ℝ}
    (positive : 0 < distance) (firstSeparated : distance ≤ ‖first‖) (secondSeparated : distance ≤ ‖second‖) :
    ‖first⁻¹ ^ 2 - second⁻¹ ^ 2‖ ≤ 2 * ‖first - second‖ / distance ^ 3 := by
  have firstNonzero := norm_pos_iff.mp (positive.trans_le firstSeparated)
  have secondNonzero := norm_pos_iff.mp (positive.trans_le secondSeparated)
  have inverseDifference : ‖first⁻¹ - second⁻¹‖ ≤ ‖first - second‖ / distance ^ 2 := by
    have identity := dist_inv_inv₀ firstNonzero secondNonzero
    simp only [dist_eq_norm] at identity
    rw [identity]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by nlinarith [mul_le_mul firstSeparated secondSeparated positive.le (norm_nonneg first)])
  have firstInverse : ‖first⁻¹‖ ≤ 1 / distance := by
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le positive firstSeparated
  have secondInverse : ‖second⁻¹‖ ≤ 1 / distance := by
    rw [norm_inv, ← one_div]
    exact one_div_le_one_div_of_le positive secondSeparated
  rw [sq_sub_sq, norm_mul, mul_comm]
  have sumBound : ‖first⁻¹ + second⁻¹‖ ≤ 2 / distance :=
    (norm_add_le _ _).trans ((add_le_add firstInverse secondInverse).trans_eq (by ring))
  exact (mul_le_mul inverseDifference sumBound (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem biotSavartKernelStrain_difference_bound {first second source : ℂ} {distance : ℝ}
    (positive : 0 < distance) (firstSeparated : distance ≤ ‖first - source‖)
    (secondSeparated : distance ≤ ‖second - source‖) :
    ‖biotSavartKernelStrain first source - biotSavartKernelStrain second source‖ ≤
      ‖first - second‖ / (Real.pi * distance ^ 3) := by
  have identity : biotSavartKernelStrain first source - biotSavartKernelStrain second source =
      -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
        ((star (first - source))⁻¹ ^ 2 - (star (second - source))⁻¹ ^ 2) := by
    simp only [biotSavartKernelStrain, div_eq_mul_inv, ← inv_pow]
    ring
  rw [identity, norm_mul]
  have coefficient : ‖-(Complex.I / ((2 * Real.pi : ℝ) : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_neg, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [coefficient]
  have estimate := inverse_square_difference_bound (first := star (first - source))
    (second := star (second - source)) positive
    (by simpa only [norm_star] using firstSeparated) (by simpa only [norm_star] using secondSeparated)
  have difference : star (first - source) - star (second - source) = star (first - second) := by
    rw [← star_sub]
    congr 1
    abel
  rw [difference, norm_star] at estimate
  exact (mul_le_mul_of_nonneg_left estimate (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans_eq (by ring)

theorem indicator_biotSavart_strain_difference_bound {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤) (density : ℝ)
    {first second : ℂ} {distance : ℝ} (positive : 0 < distance)
    (firstSeparated : ∀ source ∈ domain, distance ≤ ‖first - source‖)
    (secondSeparated : ∀ source ∈ domain, distance ≤ ‖second - source‖) :
    ‖(density • ∫ source in domain, biotSavartKernelStrain first source) -
        (density • ∫ source in domain, biotSavartKernelStrain second source)‖ ≤
      |density| * volume.real domain * ‖first - second‖ / (Real.pi * distance ^ 3) := by
  have firstIntegrable := integrableOn_biotSavartKernelStrain_of_separation measurable finite positive firstSeparated
  have secondIntegrable := integrableOn_biotSavartKernelStrain_of_separation measurable finite positive secondSeparated
  rw [← smul_sub, ← integral_sub firstIntegrable secondIntegrable, norm_smul, Real.norm_eq_abs]
  have estimate := norm_integral_le_of_norm_le (μ := volume.restrict domain)
    (f := fun source => biotSavartKernelStrain first source - biotSavartKernelStrain second source)
    (g := fun _ : ℂ => ‖first - second‖ / (Real.pi * distance ^ 3))
    (integrableOn_const.mpr (Or.inr finite)) (by
      filter_upwards [ae_restrict_mem measurable] with source member
      exact biotSavartKernelStrain_difference_bound positive (firstSeparated source member) (secondSeparated source member))
  rw [integral_const] at estimate
  exact (mul_le_mul_of_nonneg_left estimate (abs_nonneg density)).trans_eq (by
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    ring)

theorem indicator_biotSavart_fderiv_difference_bound {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤) (density : ℝ)
    {first second : ℂ} {distance : ℝ} (positive : 0 < distance)
    (firstSeparated : ∀ source ∈ domain, distance ≤ ‖first - source‖)
    (secondSeparated : ∀ source ∈ domain, distance ≤ ‖second - source‖) :
    ‖fderiv ℝ (biotSavart (domain.indicator (fun _ => density))) first -
        fderiv ℝ (biotSavart (domain.indicator (fun _ => density))) second‖ ≤
      |density| * volume.real domain * ‖first - second‖ / (Real.pi * distance ^ 3) := by
  rw [(indicator_biotSavart_hasFDerivAt_of_separation measurable finite density positive firstSeparated).fderiv,
    (indicator_biotSavart_hasFDerivAt_of_separation measurable finite density positive secondSeparated).fderiv,
    ← sub_smul, norm_smul, Complex.conjCLE_norm, mul_one]
  exact indicator_biotSavart_strain_difference_bound measurable finite density positive firstSeparated secondSeparated

theorem indicator_biotSavart_fderiv_lipschitzOn {domain region : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤) (density : ℝ)
    {distance : ℝ} (positive : 0 < distance) {bound : ℝ≥0}
    (separated : ∀ position ∈ region, ∀ source ∈ domain, distance ≤ ‖position - source‖)
    (boundLarge : |density| * volume.real domain / (Real.pi * distance ^ 3) ≤ (bound : ℝ)) :
    LipschitzOnWith bound (fderiv ℝ (biotSavart (domain.indicator (fun _ => density)))) region := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro first firstInside second secondInside
  have estimate := indicator_biotSavart_fderiv_difference_bound measurable finite density positive
    (separated first firstInside) (separated second secondInside)
  apply estimate.trans
  have multiplied := mul_le_mul_of_nonneg_right boundLarge (norm_nonneg (first - second))
  convert multiplied using 1 <;> ring

end EulerNonuniqueness.Section6
