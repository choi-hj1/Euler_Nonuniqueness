import EulerNonuniqueness.Section3.ContourComplexGreen
import EulerNonuniqueness.Section3.ContourAnalyticMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem contourPolynomialMoment_eq_domain_integral (degree : ℕ)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    contourPolynomialMoment degree data =
      ∫ position in nearCircleInterior data small, position ^ degree := by
  let conjugation : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ
  let function := fun position : ℂ => position ^ degree * star position
  let derivative := fun position : ℂ =>
    (star position) • (((degree : ℂ) * position ^ (degree - 1)) • ContinuousLinearMap.id ℝ ℂ) +
      (position ^ degree) • conjugation
  have functionContinuous : Continuous function := by fun_prop
  have derivativeContinuous : Continuous derivative := by fun_prop
  have functionDerivative (position : ℂ) : HasFDerivAt function (derivative position) position := by
    have power := (hasDerivAt_pow degree position).hasFDerivAt.restrictScalars ℝ
    have conjugate := conjugation.hasFDerivAt (x := position)
    convert power.mul conjugate using 1
    ext direction
    simp [derivative, conjugation, ContinuousLinearMap.mul_apply', mul_comm, mul_left_comm]
    <;> ring
  have barDerivative (position : ℂ) :
      (derivative position 1 + Complex.I * derivative position Complex.I) / 2 = position ^ degree := by
    simp only [derivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, conjugation, ContinuousLinearMap.coe_restrictScalars,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, one_mul, mul_one, smul_eq_mul]
    field_simp
    ring_nf
    simp [Complex.I_sq]
    <;> ring
  have green := integral_nearCircleInterior_wirtingerBar data small function derivative
    functionContinuous derivativeContinuous functionDerivative
  simp_rw [barDerivative] at green
  rw [contourPolynomialMoment_eq_integral]
  exact green.symm

end EulerNonuniqueness.Paper
