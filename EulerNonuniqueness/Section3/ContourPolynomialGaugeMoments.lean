import EulerNonuniqueness.Section3.ContourClosedPolynomialMoments
import EulerNonuniqueness.Section3.ContourAntilinearDerivative

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

theorem c1Conjugate_naturalPower_tangent_product (data : PeriodicC1HolderHalf) (degree : ℕ) (label : ℝ) :
    star (data.val.1 label) * (c1Conjugate (c1NaturalPower data degree)).val.2.val.1 label =
      (degree : ℂ) * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label) := by
  change star (data.val.1 label) * star ((c1NaturalPower data degree).val.2.val.1 label) = _
  rw [c1NaturalPower_tangent]
  simp only [star_mul, star_pow, star_natCast]
  cases degree with
  | zero => simp
  | succ degree =>
    simp only [Nat.succ_sub_one, pow_succ]
    ring

theorem contourPolynomialMoment_zero_polynomial_hasDerivAt (data : PeriodicC1HolderHalf) (degree : ℕ) :
    HasDerivAt (fun scalar : ℝ => contourPolynomialMoment 0
      (data + scalar • c1Conjugate (c1NaturalPower data degree))) 0 0 := by
  have derivative := contourPolynomialMoment_zero_line_hasDerivAt data (c1Conjugate (c1NaturalPower data degree))
  have first : IntervalIntegrable (fun label => data.val.1 label ^ degree * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have second : IntervalIntegrable (fun label => (degree : ℂ) *
      (star (data.val.1 label) ^ degree * star (data.val.2.val.1 label)))
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have identity : (∫ label in (-Real.pi)..Real.pi,
      star ((c1Conjugate (c1NaturalPower data degree)).val.1 label) * data.val.2.val.1 label +
        star (data.val.1 label) * (c1Conjugate (c1NaturalPower data degree)).val.2.val.1 label) = 0 := by
    have integrand (label : ℝ) :
        star ((c1Conjugate (c1NaturalPower data degree)).val.1 label) * data.val.2.val.1 label +
          star (data.val.1 label) * (c1Conjugate (c1NaturalPower data degree)).val.2.val.1 label =
        data.val.1 label ^ degree * data.val.2.val.1 label +
          (degree : ℂ) * (star (data.val.1 label) ^ degree * star (data.val.2.val.1 label)) := by
      rw [c1Conjugate_naturalPower_tangent_product]
      change star (star ((c1NaturalPower data degree).val.1 label)) * data.val.2.val.1 label + _ = _
      rw [star_star, c1NaturalPower_value]
      ring
    simp_rw [integrand]
    rw [intervalIntegral.integral_add first second, intervalIntegral.integral_const_mul,
      contour_value_power_mul_tangent_integral_zero]
    have conjugateZero := contour_value_power_mul_tangent_integral_zero (c1Conjugate data) degree
    change (∫ label in (-Real.pi)..Real.pi,
      star (data.val.1 label) ^ degree * star (data.val.2.val.1 label)) = 0 at conjugateZero
    rw [conjugateZero, mul_zero, add_zero]
  simpa only [identity, mul_zero] using derivative

theorem contourAreaFunctional_polynomial_hasDerivAt (data : PeriodicC1HolderHalf) (degree : ℕ) :
    HasDerivAt (fun scalar : ℝ => contourAreaFunctional
      (data + scalar • c1Conjugate (c1NaturalPower data degree))) 0 0 :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (contourPolynomialMoment_zero_polynomial_hasDerivAt data degree)

theorem contourPolynomialMoment_conjugate_integral (data : PeriodicC1HolderHalf) (degree : ℕ) :
    star (contourPolynomialMoment degree data) = (Complex.I / 2) *
      ∫ label in (-Real.pi)..Real.pi,
        data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label) := by
  have integrable : IntervalIntegrable (fun label =>
      data.val.1 label ^ degree * star (data.val.1 label) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have commutation := (Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).intervalIntegral_comp_comm integrable
  change (∫ label in (-Real.pi)..Real.pi,
      star (data.val.1 label ^ degree * star (data.val.1 label) * data.val.2.val.1 label)) =
    star (∫ label in (-Real.pi)..Real.pi,
      data.val.1 label ^ degree * star (data.val.1 label) * data.val.2.val.1 label) at commutation
  rw [contourPolynomialMoment_eq_integral]
  simp only [star_mul]
  have coefficient : star (-Complex.I / 2) = Complex.I / 2 := by simp
  rw [coefficient, ← commutation]
  have integralIdentity : (∫ label in (-Real.pi)..Real.pi,
      star (data.val.1 label ^ degree * star (data.val.1 label) * data.val.2.val.1 label)) =
      ∫ label in (-Real.pi)..Real.pi,
        data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label) := by
    apply intervalIntegral.integral_congr
    intro label _inside
    simp only [star_mul, star_star, star_pow]
    ring
  rw [integralIdentity]
  ring

theorem contour_first_moment_polynomial_integral (data : PeriodicC1HolderHalf) (degree : ℕ) :
    (∫ label in (-Real.pi)..Real.pi,
      star (data.val.1 label) ^ (degree + 1) * data.val.2.val.1 label +
        data.val.1 label ^ (degree + 1) * data.val.2.val.1 label +
        (degree : ℂ) * (data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label))) =
      -(∫ label in (-Real.pi)..Real.pi,
        data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label)) := by
  have first : IntervalIntegrable (fun label => star (data.val.1 label) ^ (degree + 1) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have second : IntervalIntegrable (fun label => data.val.1 label ^ (degree + 1) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have third : IntervalIntegrable (fun label => data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label))
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have closed := contour_conjugate_power_product_derivative_integral_zero data degree
  rw [intervalIntegral.integral_add first (third.const_mul (((degree + 1 : ℕ) : ℂ))),
    intervalIntegral.integral_const_mul] at closed
  rw [intervalIntegral.integral_add (first.add second) (third.const_mul (degree : ℂ)),
    intervalIntegral.integral_add first second, intervalIntegral.integral_const_mul]
  have holomorphic := contour_value_power_mul_tangent_integral_zero data (degree + 1)
  push_cast at closed
  linear_combination closed + holomorphic

theorem contourPolynomialMoment_one_polynomial_hasDerivAt (data : PeriodicC1HolderHalf) (degree : ℕ) :
    HasDerivAt (fun scalar : ℝ => contourPolynomialMoment 1
      (data + scalar • c1Conjugate (c1NaturalPower data degree)))
      (star (contourPolynomialMoment degree data)) 0 := by
  have derivative := contourPolynomialMoment_one_line_hasDerivAt data (c1Conjugate (c1NaturalPower data degree))
  have identity : (∫ label in (-Real.pi)..Real.pi,
      (c1Conjugate (c1NaturalPower data degree)).val.1 label * star (data.val.1 label) * data.val.2.val.1 label +
        data.val.1 label * star ((c1Conjugate (c1NaturalPower data degree)).val.1 label) * data.val.2.val.1 label +
        data.val.1 label * star (data.val.1 label) * (c1Conjugate (c1NaturalPower data degree)).val.2.val.1 label) =
      -(∫ label in (-Real.pi)..Real.pi,
        data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label)) := by
    convert contour_first_moment_polynomial_integral data degree using 1
    apply intervalIntegral.integral_congr
    intro label _inside
    dsimp only
    rw [mul_assoc (data.val.1 label) (star (data.val.1 label)), c1Conjugate_naturalPower_tangent_product]
    change star ((c1NaturalPower data degree).val.1 label) * star (data.val.1 label) * data.val.2.val.1 label +
      data.val.1 label * star (star ((c1NaturalPower data degree).val.1 label)) * data.val.2.val.1 label + _ = _
    rw [star_star, c1NaturalPower_value, star_pow, pow_succ, pow_succ]
    ring
  rw [identity] at derivative
  rw [contourPolynomialMoment_conjugate_integral]
  convert derivative using 1 <;> ring

end EulerNonuniqueness.Paper
