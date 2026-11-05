import EulerNonuniqueness.Section6.VorticityStrainMultipole

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

def vorticityComplexStrain (vorticity : Vorticity) (location : ℂ) : ℂ :=
  ∫ source, vorticity source • biotSavartKernelStrain location source

theorem vorticityComplexStrain_cauchy_identity (vorticity : Vorticity) (location : ℂ) :
    vorticityComplexStrain vorticity location =
      -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
        star (∫ source, vorticity source • (1 / (location - source) ^ 2 : ℂ)) := by
  have identity : (fun source => vorticity source • biotSavartKernelStrain location source) =
      fun source => -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
        star (vorticity source • (1 / (location - source) ^ 2 : ℂ)) := by
    funext source
    simp only [biotSavartKernelStrain, Complex.real_smul, star_mul, star_div₀, star_pow,
      star_one, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [vorticityComplexStrain, identity, integral_const_mul]
  congr 1
  exact integral_conj

theorem vorticityComplexStrain_multipole_bound {vorticity : Vorticity}
    (integrable : Integrable vorticity) {center location : ℂ} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (supported : Function.support vorticity ⊆ Metric.closedBall center radius)
    (locationPositive : 0 < ‖location - center‖) (separated : 2 * radius ≤ ‖location - center‖) :
    ‖vorticityComplexStrain vorticity location +
        (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (
          (∫ source, vorticity source • (1 : ℂ)) / (location - center) ^ 2 +
          2 * (∫ source, vorticity source • (source - center)) / (location - center) ^ 3 +
          3 * (∫ source, vorticity source • (source - center) ^ 2) / (location - center) ^ 4)‖ ≤
      88 * radius ^ 3 * (∫ source, |vorticity source|) / (Real.pi * ‖location - center‖ ^ 5) := by
  have estimate := vorticity_cauchy_strain_multipole_bound integrable radiusNonnegative supported locationPositive separated
  have identity : vorticityComplexStrain vorticity location +
      (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (
        (∫ source, vorticity source • (1 : ℂ)) / (location - center) ^ 2 +
        2 * (∫ source, vorticity source • (source - center)) / (location - center) ^ 3 +
        3 * (∫ source, vorticity source • (source - center) ^ 2) / (location - center) ^ 4) =
      -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (
        (∫ source, vorticity source • (1 / (location - source) ^ 2 : ℂ)) -
        (∫ source, vorticity source • (1 : ℂ)) / (location - center) ^ 2 -
        2 * (∫ source, vorticity source • (source - center)) / (location - center) ^ 3 -
        3 * (∫ source, vorticity source • (source - center) ^ 2) / (location - center) ^ 4) := by
    rw [vorticityComplexStrain_cauchy_identity]
    simp only [star_sub, star_add]
    ring
  rw [identity, norm_mul, norm_neg, norm_star]
  have coefficient : ‖Complex.I / ((2 * Real.pi : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [coefficient]
  exact (mul_le_mul_of_nonneg_left estimate (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans_eq (by ring)

theorem vorticityComplexStrain_zeroMean_multipole_bound {vorticity : Vorticity}
    (integrable : Integrable vorticity) (zeroMean : (∫ source, vorticity source) = 0)
    {center location : ℂ} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (supported : Function.support vorticity ⊆ Metric.closedBall center radius)
    (locationPositive : 0 < ‖location - center‖) (separated : 2 * radius ≤ ‖location - center‖) :
    ‖vorticityComplexStrain vorticity location +
        (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (
          2 * (∫ source, vorticity source • (source - center)) / (location - center) ^ 3 +
          3 * (∫ source, vorticity source • (source - center) ^ 2) / (location - center) ^ 4)‖ ≤
      88 * radius ^ 3 * (∫ source, |vorticity source|) / (Real.pi * ‖location - center‖ ^ 5) := by
  have estimate := vorticityComplexStrain_multipole_bound integrable radiusNonnegative supported locationPositive separated
  simpa only [integral_smul_const, zeroMean, zero_smul, zero_div, zero_add] using estimate

end EulerNonuniqueness.Section6
