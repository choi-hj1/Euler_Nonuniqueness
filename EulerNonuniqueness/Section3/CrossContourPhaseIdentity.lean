import EulerNonuniqueness.Section3.ContourDynamics

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

def pointContourVelocity (curve tangent : ℝ → ℂ) (point : ℂ) (lower upper : ℝ) : ℂ :=
  -(1 / (2 * Real.pi)) •
    ∫ source in lower..upper, Real.log ‖curve source - point‖ • tangent source

def pointContourPhase (curve : ℝ → ℂ) (point : ℂ) (source : ℝ) : ℂ :=
  (curve source - point) / star (curve source - point)

theorem point_contour_log_derivative {curve : ℝ → ℂ} {tangent point : ℂ} {source : ℝ}
    (derivative : HasDerivAt curve tangent source) (separated : curve source - point ≠ 0) :
    HasDerivAt (fun label => Real.log ‖curve label - point‖)
      ((tangent / (curve source - point)).re) source := by
  have square_derivative := (derivative.sub_const point).norm_sq
  have log_derivative := (square_derivative.log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr separated))).div_const 2
  convert log_derivative using 1
  · funext label
    rw [Real.log_pow]
    simp
  · rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.normSq_eq_norm_sq]
    ring

theorem point_contour_log_product_derivative {curve tangent : ℝ → ℂ} {point : ℂ} {source : ℝ}
    (derivative : HasDerivAt curve (tangent source) source)
    (separated : curve source - point ≠ 0) :
    HasDerivAt (fun label => Real.log ‖curve label - point‖ • (curve label - point))
      (Real.log ‖curve source - point‖ • tangent source +
        (tangent source + pointContourPhase curve point source * star (tangent source)) / 2) source := by
  have product := (point_contour_log_derivative derivative separated).smul (derivative.sub_const point)
  convert product using 1
  rw [real_div_smul_eq_phase separated]
  rfl

theorem pointContourVelocity_eq_phase_integral {curve tangent : ℝ → ℂ} {point : ℂ}
    {lower upper : ℝ} (ordered : lower ≤ upper)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (derivative : ∀ source ∈ Icc lower upper, HasDerivAt curve (tangent source) source)
    (separated : ∀ source ∈ Icc lower upper, curve source - point ≠ 0)
    (closed : curve lower = curve upper) :
    pointContourVelocity curve tangent point lower upper =
      (1 / (4 * Real.pi)) •
        ∫ source in lower..upper, pointContourPhase curve point source * star (tangent source) := by
  have difference_continuous : Continuous (fun source => curve source - point) := curve_continuous.sub continuous_const
  have log_continuous : ContinuousOn (fun source => Real.log ‖curve source - point‖) (Icc lower upper) :=
    difference_continuous.norm.continuousOn.log (fun source source_mem => norm_ne_zero_iff.mpr (separated source source_mem))
  have log_integrable : IntervalIntegrable
      (fun source => Real.log ‖curve source - point‖ • tangent source) volume lower upper :=
    (log_continuous.smul tangent_continuous.continuousOn).intervalIntegrable_of_Icc ordered
  have tangent_integrable : IntervalIntegrable tangent volume lower upper := tangent_continuous.intervalIntegrable _ _
  have phase_continuous : ContinuousOn (fun source => pointContourPhase curve point source * star (tangent source))
      (Icc lower upper) := by
    apply (difference_continuous.continuousOn.div difference_continuous.star.continuousOn
      (fun source source_mem => star_ne_zero.mpr (separated source source_mem))).mul tangent_continuous.star.continuousOn
  have phase_integrable : IntervalIntegrable
      (fun source => pointContourPhase curve point source * star (tangent source)) volume lower upper :=
    phase_continuous.intervalIntegrable_of_Icc ordered
  have boundary := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun source source_mem => point_contour_log_product_derivative
      (derivative source (by simpa only [uIcc_of_le ordered] using source_mem))
      (separated source (by simpa only [uIcc_of_le ordered] using source_mem)))
    (log_integrable.add ((tangent_integrable.add phase_integrable).div_const (2 : ℂ)))
  rw [intervalIntegral.integral_add log_integrable ((tangent_integrable.add phase_integrable).div_const (2 : ℂ)),
    intervalIntegral.integral_div, intervalIntegral.integral_add tangent_integrable phase_integrable] at boundary
  have tangent_integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun source source_mem => derivative source (by simpa only [uIcc_of_le ordered] using source_mem)) tangent_integrable
  rw [tangent_integral] at boundary
  simp only [closed, sub_self, zero_add] at boundary
  have identity : (∫ source in lower..upper, Real.log ‖curve source - point‖ • tangent source) =
      -((∫ source in lower..upper, pointContourPhase curve point source * star (tangent source)) / 2) :=
    eq_neg_iff_add_eq_zero.mpr boundary
  rw [pointContourVelocity, identity, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

end

end EulerNonuniqueness.Paper
