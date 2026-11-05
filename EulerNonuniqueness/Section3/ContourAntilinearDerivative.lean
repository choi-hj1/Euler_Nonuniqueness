import EulerNonuniqueness.Section3.ContourPolynomialMomentLine

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance antilinearDerivativeHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance antilinearDerivativeC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem contourPolynomialMoment_zero_antilinear_hasDerivAt (data : PeriodicC1HolderHalf) :
    HasDerivAt (fun scalar : ℝ => contourPolynomialMoment 0 (data + scalar • c1Conjugate data)) 0 0 := by
  have derivative := contourPolynomialMoment_zero_line_hasDerivAt data (c1Conjugate data)
  have integrableFirst : IntervalIntegrable (fun label => data.val.1 label * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi := (data.val.1.continuous.mul data.val.2.val.1.continuous).intervalIntegrable _ _
  have integrableSecond : IntervalIntegrable (fun label => star (data.val.1 label) * star (data.val.2.val.1 label))
      volume (-Real.pi) Real.pi := (data.val.1.continuous.star.mul data.val.2.val.1.continuous.star).intervalIntegrable _ _
  have integral : (∫ label in (-Real.pi)..Real.pi,
      star ((c1Conjugate data).val.1 label) * data.val.2.val.1 label +
        star (data.val.1 label) * (c1Conjugate data).val.2.val.1 label) = 0 := by
    change (∫ label in (-Real.pi)..Real.pi,
      star (star (data.val.1 label)) * data.val.2.val.1 label +
        star (data.val.1 label) * star (data.val.2.val.1 label)) = 0
    simp only [star_star]
    rw [intervalIntegral.integral_add integrableFirst integrableSecond,
      contour_value_mul_tangent_integral_zero]
    have conjugateZero := contour_value_mul_tangent_integral_zero (c1Conjugate data)
    change (∫ label in (-Real.pi)..Real.pi, star (data.val.1 label) * star (data.val.2.val.1 label)) = 0 at conjugateZero
    rw [conjugateZero, add_zero]
  simpa only [integral, mul_zero] using derivative

theorem contourAreaFunctional_antilinear_hasDerivAt (data : PeriodicC1HolderHalf) :
    HasDerivAt (fun scalar : ℝ => contourAreaFunctional (data + scalar • c1Conjugate data)) 0 0 := by
  have derivative := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (contourPolynomialMoment_zero_antilinear_hasDerivAt data)
  exact derivative

theorem contour_first_moment_antilinear_integral (data : PeriodicC1HolderHalf) :
    (∫ label in (-Real.pi)..Real.pi,
      star (data.val.1 label) ^ 2 * data.val.2.val.1 label +
        data.val.1 label ^ 2 * data.val.2.val.1 label +
        data.val.1 label * star (data.val.1 label) * star (data.val.2.val.1 label)) =
      -(∫ label in (-Real.pi)..Real.pi,
        data.val.1 label * star (data.val.1 label) * star (data.val.2.val.1 label)) := by
  have first : IntervalIntegrable (fun label => star (data.val.1 label) ^ 2 * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have second : IntervalIntegrable (fun label => data.val.1 label ^ 2 * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have third : IntervalIntegrable (fun label => data.val.1 label * star (data.val.1 label) * star (data.val.2.val.1 label))
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have closed := contour_conjugate_square_derivative_integral_zero data
  rw [intervalIntegral.integral_add first (third.const_mul (2 : ℂ)), intervalIntegral.integral_const_mul] at closed
  rw [intervalIntegral.integral_add (first.add second) third, intervalIntegral.integral_add first second]
  have cubic := contour_value_sq_mul_tangent_integral_zero data
  linear_combination closed + cubic

theorem contourPolynomialMoment_one_conjugate (data : PeriodicC1HolderHalf) :
    star (contourPolynomialMoment 1 data) = (Complex.I / 2) *
      ∫ label in (-Real.pi)..Real.pi,
        data.val.1 label * star (data.val.1 label) * star (data.val.2.val.1 label) := by
  have integrable : IntervalIntegrable (fun label => data.val.1 label * star (data.val.1 label) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have commutation := (Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).intervalIntegral_comp_comm integrable
  change (∫ label in (-Real.pi)..Real.pi, star (data.val.1 label * star (data.val.1 label) * data.val.2.val.1 label)) =
    star (∫ label in (-Real.pi)..Real.pi, data.val.1 label * star (data.val.1 label) * data.val.2.val.1 label) at commutation
  rw [contourPolynomialMoment_eq_integral]
  simp only [pow_one, star_mul]
  have coefficient : star (-Complex.I / 2) = Complex.I / 2 := by simp
  rw [coefficient, ← commutation]
  have integralIdentity : (∫ label in (-Real.pi)..Real.pi,
      star (data.val.1 label * star (data.val.1 label) * data.val.2.val.1 label)) =
      ∫ label in (-Real.pi)..Real.pi, data.val.1 label * star (data.val.1 label) * star (data.val.2.val.1 label) := by
    apply intervalIntegral.integral_congr
    intro label _inside
    simp only [star_mul, star_star]
    ring
  rw [integralIdentity]
  ring

theorem contourPolynomialMoment_one_antilinear_hasDerivAt (data : PeriodicC1HolderHalf) :
    HasDerivAt (fun scalar : ℝ => contourPolynomialMoment 1 (data + scalar • c1Conjugate data))
      (star (contourPolynomialMoment 1 data)) 0 := by
  have derivative := contourPolynomialMoment_one_line_hasDerivAt data (c1Conjugate data)
  have integralIdentity : (∫ label in (-Real.pi)..Real.pi,
      (c1Conjugate data).val.1 label * star (data.val.1 label) * data.val.2.val.1 label +
        data.val.1 label * star ((c1Conjugate data).val.1 label) * data.val.2.val.1 label +
        data.val.1 label * star (data.val.1 label) * (c1Conjugate data).val.2.val.1 label) =
      -(∫ label in (-Real.pi)..Real.pi,
        data.val.1 label * star (data.val.1 label) * star (data.val.2.val.1 label)) := by
    convert contour_first_moment_antilinear_integral data using 1
    apply intervalIntegral.integral_congr
    intro label _inside
    change star (data.val.1 label) * star (data.val.1 label) * data.val.2.val.1 label +
      data.val.1 label * star (star (data.val.1 label)) * data.val.2.val.1 label +
      data.val.1 label * star (data.val.1 label) * star (data.val.2.val.1 label) = _
    rw [star_star]
    ring
  rw [integralIdentity] at derivative
  rw [contourPolynomialMoment_one_conjugate]
  convert derivative using 1 <;> ring

end EulerNonuniqueness.Paper
