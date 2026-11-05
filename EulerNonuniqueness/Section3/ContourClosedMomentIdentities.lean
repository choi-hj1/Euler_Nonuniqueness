import EulerNonuniqueness.Section3.ContourAnalyticCentroid
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem contour_tangent_integral_zero (data : PeriodicC1HolderHalf) :
    (∫ label in (-Real.pi)..Real.pi, data.val.2.val.1 label) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun label _ => PeriodicC1HolderHalf.hasDerivAt data label)
    (data.val.2.val.1.continuous.intervalIntegrable _ _)]
  have periodic := PeriodicC1HolderHalf.periodic data (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at periodic
  rw [periodic, sub_self]

theorem contour_value_mul_tangent_integral_zero (data : PeriodicC1HolderHalf) :
    (∫ label in (-Real.pi)..Real.pi, data.val.1 label * data.val.2.val.1 label) = 0 := by
  have derivative (label : ℝ) : HasDerivAt (fun current => data.val.1 current ^ 2)
      ((2 : ℂ) * (data.val.1 label * data.val.2.val.1 label)) label := by
    convert (PeriodicC1HolderHalf.hasDerivAt data label).mul (PeriodicC1HolderHalf.hasDerivAt data label) using 1
    · funext current
      ring
    · ring
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun label _ => derivative label)
    ((continuous_const.mul (data.val.1.continuous.mul data.val.2.val.1.continuous)).intervalIntegrable (-Real.pi) Real.pi)
  have periodic := PeriodicC1HolderHalf.periodic data (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at periodic
  rw [intervalIntegral.integral_const_mul, periodic, sub_self] at integral
  exact (mul_eq_zero.mp integral).resolve_left (by norm_num)

theorem contour_conjugate_mul_tangent_real_integral_zero (data : PeriodicC1HolderHalf) :
    (∫ label in (-Real.pi)..Real.pi, (star (data.val.1 label) * data.val.2.val.1 label).re) = 0 := by
  have innerIdentity (label : ℝ) : @inner ℝ ℂ _ (data.val.1 label) (data.val.2.val.1 label) =
      (star (data.val.1 label) * data.val.2.val.1 label).re := by
    rw [Complex.inner]
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have derivative (label : ℝ) : HasDerivAt (fun current => ‖data.val.1 current‖ ^ 2)
      (2 * (star (data.val.1 label) * data.val.2.val.1 label).re) label := by
    simpa only [innerIdentity] using (PeriodicC1HolderHalf.hasDerivAt data label).norm_sq
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun label _ => derivative label)
    ((continuous_const.mul (Complex.continuous_re.comp (data.val.1.continuous.star.mul data.val.2.val.1.continuous))).intervalIntegrable (-Real.pi) Real.pi)
  have periodic := PeriodicC1HolderHalf.periodic data (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at periodic
  rw [intervalIntegral.integral_const_mul, periodic, sub_self] at integral
  linarith

theorem contourPolynomialMoment_zero_real (data : PeriodicC1HolderHalf) :
    contourPolynomialMoment 0 data = (contourAreaFunctional data : ℂ) := by
  have integrable : IntervalIntegrable (fun label => star (data.val.1 label) * data.val.2.val.1 label)
      volume (-Real.pi) Real.pi :=
    (data.val.1.continuous.star.mul data.val.2.val.1.continuous).intervalIntegrable _ _
  have integralReal : (∫ label in (-Real.pi)..Real.pi, star (data.val.1 label) * data.val.2.val.1 label).re = 0 := by
    change Complex.reCLM (∫ label in (-Real.pi)..Real.pi, star (data.val.1 label) * data.val.2.val.1 label) = 0
    rw [← Complex.reCLM.intervalIntegral_comp_comm integrable]
    exact contour_conjugate_mul_tangent_real_integral_zero data
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im, contourPolynomialMoment_eq_integral]
    simp only [pow_zero, one_mul]
    simp only [Complex.mul_im, Complex.div_re, Complex.div_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im, neg_zero, zero_mul,
      mul_zero, zero_sub, integralReal]
    norm_num

end EulerNonuniqueness.Paper
