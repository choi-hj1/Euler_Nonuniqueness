import EulerNonuniqueness.Section3.ContourCentroidTranslation

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance momentRealScalingC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem contourPolynomialMoment_real_smul (degree : ℕ) (data : PeriodicC1HolderHalf) (scalar : ℝ) :
    contourPolynomialMoment degree (scalar • data) =
      (scalar : ℂ) ^ (degree + 2) * contourPolynomialMoment degree data := by
  rw [contourPolynomialMoment_eq_integral, contourPolynomialMoment_eq_integral]
  have integrand : (fun label => ((scalar • data).val.1 label) ^ degree *
      star ((scalar • data).val.1 label) * (scalar • data).val.2.val.1 label) =
      fun label => (scalar : ℂ) ^ (degree + 2) *
        (data.val.1 label ^ degree * star (data.val.1 label) * data.val.2.val.1 label) := by
    funext label
    change ((scalar : ℂ) * data.val.1 label) ^ degree * star ((scalar : ℂ) * data.val.1 label) *
      ((scalar : ℂ) * data.val.2.val.1 label) = _
    rw [mul_pow, star_mul, Complex.star_def, Complex.conj_ofReal]
    simp only [pow_add, pow_two]
    ring
  rw [integrand, intervalIntegral.integral_const_mul]
  ring

theorem contourAreaFunctional_real_smul (data : PeriodicC1HolderHalf) (scalar : ℝ) :
    contourAreaFunctional (scalar • data) = scalar ^ 2 * contourAreaFunctional data := by
  simp only [contourAreaFunctional, contourPolynomialMoment_real_smul, zero_add]
  rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem contourCentroidFunctional_real_smul (data : PeriodicC1HolderHalf) (scalar : ℝ) (nonzero : scalar ≠ 0) :
    contourCentroidFunctional (scalar • data) = scalar • contourCentroidFunctional data := by
  rw [contourCentroidFunctional, contourPolynomialMoment_real_smul, contourAreaFunctional_real_smul]
  simp only [show (1 + 2 : ℕ) = 3 by norm_num, Complex.ofReal_mul, Complex.ofReal_pow, Complex.real_smul,
    contourCentroidFunctional]
  have scalarNonzero : (scalar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  by_cases area : contourAreaFunctional data = 0
  · simp [area]
  · have areaNonzero : (contourAreaFunctional data : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr area
    field_simp
    <;> ring

end EulerNonuniqueness.Paper
