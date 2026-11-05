import EulerNonuniqueness.Section3.ContourClosedMomentIdentities

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem contourPolynomialMoment_zero_translate (data : PeriodicC1HolderHalf) (translation : ℂ) :
    contourPolynomialMoment 0 (data + c1Constant translation) = contourPolynomialMoment 0 data := by
  have first : IntervalIntegrable (fun label => star (data.val.1 label) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi :=
    (data.val.1.continuous.star.mul data.val.2.val.1.continuous).intervalIntegrable _ _
  have second : IntervalIntegrable (fun label => star translation * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi :=
    (continuous_const.mul data.val.2.val.1.continuous).intervalIntegrable _ _
  rw [contourPolynomialMoment_eq_integral, contourPolynomialMoment_eq_integral]
  simp only [pow_zero, one_mul]
  have integrand : (fun label => star ((data + c1Constant translation).val.1 label) *
      (data + c1Constant translation).val.2.val.1 label) =
      fun label => star (data.val.1 label) * data.val.2.val.1 label + star translation * data.val.2.val.1 label := by
    funext label
    change star (data.val.1 label + translation) * (data.val.2.val.1 label + 0) = _
    rw [star_add, add_zero, add_mul]
  rw [integrand, intervalIntegral.integral_add first second, intervalIntegral.integral_const_mul,
    contour_tangent_integral_zero, mul_zero, add_zero]

theorem contourAreaFunctional_translate (data : PeriodicC1HolderHalf) (translation : ℂ) :
    contourAreaFunctional (data + c1Constant translation) = contourAreaFunctional data := by
  exact congrArg Complex.re (contourPolynomialMoment_zero_translate data translation)

theorem contourPolynomialMoment_one_translate (data : PeriodicC1HolderHalf) (translation : ℂ) :
    contourPolynomialMoment 1 (data + c1Constant translation) =
      contourPolynomialMoment 1 data + translation * contourPolynomialMoment 0 data := by
  have cubic : IntervalIntegrable (fun label => data.val.1 label * star (data.val.1 label) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi :=
    ((data.val.1.continuous.mul data.val.1.continuous.star).mul data.val.2.val.1.continuous).intervalIntegrable _ _
  have areaTerm : IntervalIntegrable (fun label => translation * (star (data.val.1 label) * data.val.2.val.1 label))
      volume (-Real.pi) Real.pi :=
    (continuous_const.mul (data.val.1.continuous.star.mul data.val.2.val.1.continuous)).intervalIntegrable _ _
  have quadratic : IntervalIntegrable (fun label => star translation * (data.val.1 label * data.val.2.val.1 label))
      volume (-Real.pi) Real.pi :=
    (continuous_const.mul (data.val.1.continuous.mul data.val.2.val.1.continuous)).intervalIntegrable _ _
  have linearTerm : IntervalIntegrable (fun label => (translation * star translation) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi :=
    (continuous_const.mul data.val.2.val.1.continuous).intervalIntegrable _ _
  rw [contourPolynomialMoment_eq_integral, contourPolynomialMoment_eq_integral, contourPolynomialMoment_eq_integral]
  simp only [pow_one, pow_zero, one_mul]
  have integrand : (fun label => (data + c1Constant translation).val.1 label *
      star ((data + c1Constant translation).val.1 label) * (data + c1Constant translation).val.2.val.1 label) =
      fun label => ((data.val.1 label * star (data.val.1 label) * data.val.2.val.1 label +
        translation * (star (data.val.1 label) * data.val.2.val.1 label)) +
        star translation * (data.val.1 label * data.val.2.val.1 label)) +
        (translation * star translation) * data.val.2.val.1 label := by
    funext label
    change (data.val.1 label + translation) * star (data.val.1 label + translation) *
      (data.val.2.val.1 label + 0) = _
    rw [star_add]
    ring
  rw [integrand, intervalIntegral.integral_add ((cubic.add areaTerm).add quadratic) linearTerm,
    intervalIntegral.integral_add (cubic.add areaTerm) quadratic, intervalIntegral.integral_add cubic areaTerm]
  simp only [intervalIntegral.integral_const_mul, contour_value_mul_tangent_integral_zero,
    contour_tangent_integral_zero, mul_zero, add_zero]
  ring

theorem contourCentroidFunctional_translate (data : PeriodicC1HolderHalf) (translation : ℂ)
    (nonzero : contourAreaFunctional data ≠ 0) :
    contourCentroidFunctional (data + c1Constant translation) = contourCentroidFunctional data + translation := by
  rw [contourCentroidFunctional, contourCentroidFunctional, contourPolynomialMoment_one_translate,
    contourAreaFunctional_translate, contourPolynomialMoment_zero_real]
  have complexNonzero : (contourAreaFunctional data : ℂ) ≠ 0 := by exact_mod_cast nonzero
  field_simp

end EulerNonuniqueness.Paper
