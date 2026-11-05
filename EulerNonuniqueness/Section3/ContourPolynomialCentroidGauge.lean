import EulerNonuniqueness.Section3.ContourPolynomialGaugeMoments
import EulerNonuniqueness.Section3.AreaNormalizedForcingJet
import EulerNonuniqueness.Section3.ContourCentroidGauge

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance polynomialCentroidC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourPolynomialMoment_zero_complexPolynomial_hasDerivAt
    (data : PeriodicC1HolderHalf) (degree : ℕ) (coefficient : ℂ) :
    HasDerivAt (fun scalar : ℝ => contourPolynomialMoment 0
      (data + scalar • (coefficient • c1Conjugate (c1NaturalPower data degree)))) 0 0 := by
  have derivative := contourPolynomialMoment_zero_line_hasDerivAt data
    (coefficient • c1Conjugate (c1NaturalPower data degree))
  have first : IntervalIntegrable (fun label => data.val.1 label ^ degree * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have second : IntervalIntegrable (fun label => star (data.val.1 label) ^ degree * star (data.val.2.val.1 label))
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have integrand (label : ℝ) :
      star ((coefficient • c1Conjugate (c1NaturalPower data degree)).val.1 label) * data.val.2.val.1 label +
        star (data.val.1 label) * (coefficient • c1Conjugate (c1NaturalPower data degree)).val.2.val.1 label =
      star coefficient * (data.val.1 label ^ degree * data.val.2.val.1 label) +
        (coefficient * (degree : ℂ)) * (star (data.val.1 label) ^ degree * star (data.val.2.val.1 label)) := by
    rw [complexC1Holder_smul_value, complexC1Holder_smul_tangent]
    rw [mul_left_comm (star (data.val.1 label)) coefficient,
      c1Conjugate_naturalPower_tangent_product]
    change star (coefficient * star ((c1NaturalPower data degree).val.1 label)) * data.val.2.val.1 label + _ = _
    rw [star_mul, star_star, c1NaturalPower_value]
    ring
  have zero : (∫ label in (-Real.pi)..Real.pi,
      star ((coefficient • c1Conjugate (c1NaturalPower data degree)).val.1 label) * data.val.2.val.1 label +
        star (data.val.1 label) * (coefficient • c1Conjugate (c1NaturalPower data degree)).val.2.val.1 label) = 0 := by
    simp_rw [integrand]
    rw [intervalIntegral.integral_add (first.const_mul (star coefficient)) (second.const_mul (coefficient * (degree : ℂ))),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      contour_value_power_mul_tangent_integral_zero]
    have conjugateZero := contour_value_power_mul_tangent_integral_zero (c1Conjugate data) degree
    change (∫ label in (-Real.pi)..Real.pi,
      star (data.val.1 label) ^ degree * star (data.val.2.val.1 label)) = 0 at conjugateZero
    rw [conjugateZero]
    simp
  simpa only [zero, mul_zero] using derivative

theorem contourAreaFunctional_complexPolynomial_hasDerivAt
    (data : PeriodicC1HolderHalf) (degree : ℕ) (coefficient : ℂ) :
    HasDerivAt (fun scalar : ℝ => contourAreaFunctional
      (data + scalar • (coefficient • c1Conjugate (c1NaturalPower data degree)))) 0 0 :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
    (contourPolynomialMoment_zero_complexPolynomial_hasDerivAt data degree coefficient)

theorem contourPolynomialMoment_one_complexPolynomial_hasDerivAt
    (data : PeriodicC1HolderHalf) (degree : ℕ) (coefficient : ℂ) :
    HasDerivAt (fun scalar : ℝ => contourPolynomialMoment 1
      (data + scalar • (coefficient • c1Conjugate (c1NaturalPower data degree))))
      (coefficient * star (contourPolynomialMoment degree data)) 0 := by
  have derivative := contourPolynomialMoment_one_line_hasDerivAt data
    (coefficient • c1Conjugate (c1NaturalPower data degree))
  let whole := fun label => star (data.val.1 label) ^ (degree + 1) * data.val.2.val.1 label +
    data.val.1 label ^ (degree + 1) * data.val.2.val.1 label +
    (degree : ℂ) * (data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label))
  have wholeIntegrable : IntervalIntegrable whole volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    dsimp only [whole]
    fun_prop
  have holomorphicIntegrable : IntervalIntegrable (fun label => data.val.1 label ^ (degree + 1) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi := by apply Continuous.intervalIntegrable; fun_prop
  have integrand (label : ℝ) :
      (coefficient • c1Conjugate (c1NaturalPower data degree)).val.1 label * star (data.val.1 label) * data.val.2.val.1 label +
        data.val.1 label * star ((coefficient • c1Conjugate (c1NaturalPower data degree)).val.1 label) * data.val.2.val.1 label +
        data.val.1 label * star (data.val.1 label) * (coefficient • c1Conjugate (c1NaturalPower data degree)).val.2.val.1 label =
      coefficient * whole label + (star coefficient - coefficient) *
        (data.val.1 label ^ (degree + 1) * data.val.2.val.1 label) := by
    simp only [complexC1Holder_smul_value, complexC1Holder_smul_tangent]
    rw [mul_assoc (data.val.1 label) (star (data.val.1 label)),
      mul_left_comm (star (data.val.1 label)) coefficient,
      c1Conjugate_naturalPower_tangent_product]
    change (coefficient * star ((c1NaturalPower data degree).val.1 label)) * star (data.val.1 label) * data.val.2.val.1 label +
      data.val.1 label * star (coefficient * star ((c1NaturalPower data degree).val.1 label)) * data.val.2.val.1 label + _ = _
    simp only [c1NaturalPower_value, star_mul, star_star, star_pow, whole, pow_succ]
    ring
  simp_rw [integrand] at derivative
  rw [intervalIntegral.integral_add (wholeIntegrable.const_mul coefficient)
      (holomorphicIntegrable.const_mul (star coefficient - coefficient)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at derivative
  have wholeIdentity := contour_first_moment_polynomial_integral data degree
  change (∫ label in (-Real.pi)..Real.pi, whole label) = _ at wholeIdentity
  rw [wholeIdentity, contour_value_power_mul_tangent_integral_zero] at derivative
  rw [contourPolynomialMoment_conjugate_integral]
  convert derivative using 1 <;> ring

theorem contourCentroidFunctional_derivative_complexPolynomial
    (data : PeriodicC1HolderHalf) (degree : ℕ) (coefficient : ℂ)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    fderiv ℝ contourCentroidFunctional data
      (coefficient • c1Conjugate (c1NaturalPower data degree)) =
      coefficient * (star (contourPolynomialMoment degree data) / (contourAreaFunctional data : ℂ)) := by
  have momentJet := contourPolynomialMoment_one_complexPolynomial_hasDerivAt data degree coefficient
  have areaJet := contourAreaFunctional_complexPolynomial_hasDerivAt data degree coefficient
  have denominatorJet := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 areaJet
  have nonzero : (contourAreaFunctional data : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (contourAreaFunctional_pos data small).ne'
  have denominatorNonzero :
      (contourAreaFunctional (data + (0 : ℝ) • (coefficient • c1Conjugate (c1NaturalPower data degree))) : ℂ) ≠ 0 := by
    simpa only [zero_smul, add_zero] using nonzero
  have quotientJet := momentJet.div denominatorJet denominatorNonzero
  have outer : HasFDerivAt contourCentroidFunctional (fderiv ℝ contourCentroidFunctional data)
      (data + (0 : ℝ) • (coefficient • c1Conjugate (c1NaturalPower data degree))) := by
    simpa only [zero_smul, add_zero] using (analyticAt_contourCentroidFunctional data small).differentiableAt.hasFDerivAt
  have actual := outer.comp_hasDerivAt 0
    (contour_affine_line_hasDerivAt data (coefficient • c1Conjugate (c1NaturalPower data degree)))
  change HasDerivAt (fun scalar : ℝ => contourPolynomialMoment 1
      (data + scalar • (coefficient • c1Conjugate (c1NaturalPower data degree))) /
      (contourAreaFunctional (data + scalar • (coefficient • c1Conjugate (c1NaturalPower data degree))) : ℂ))
      (fderiv ℝ contourCentroidFunctional data (coefficient • c1Conjugate (c1NaturalPower data degree))) 0 at actual
  have identity := actual.unique quotientJet
  simp only [zero_smul, add_zero, map_zero, zero_mul, sub_zero] at identity
  rw [identity]
  field_simp
  <;> ring

theorem contourCentroidGaugeProjection_complexPolynomial
    (data : PeriodicC1HolderHalf) (degree : ℕ) (coefficient : ℂ)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    contourCentroidGaugeProjection data (coefficient • c1Conjugate (c1NaturalPower data (degree + 1))) =
      coefficient • areaNormalizedAntiholomorphicForcing degree data := by
  rw [contourCentroidGaugeProjection_apply, contourCentroidFunctional_derivative_complexPolynomial data (degree + 1) coefficient small]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (coefficient • c1Conjugate (c1NaturalPower data (degree + 1))).val.1 label -
    (c1Constant (coefficient * (star (contourPolynomialMoment (degree + 1) data) /
      (contourAreaFunctional data : ℂ)))).val.1 label = _
  rw [complexC1Holder_smul_value, c1Constant_value, complexC1Holder_smul_value]
  change coefficient * (c1Conjugate (c1NaturalPower data (degree + 1))).val.1 label -
      coefficient * (star (contourPolynomialMoment (degree + 1) data) / (contourAreaFunctional data : ℂ)) =
    coefficient * ((c1Conjugate (c1NaturalPower data (degree + 1))).val.1 label -
      (c1Constant (star (contourPolynomialMoment (degree + 1) data) / (contourAreaFunctional data : ℂ))).val.1 label)
  rw [c1Constant_value]
  ring

end EulerNonuniqueness.Paper
