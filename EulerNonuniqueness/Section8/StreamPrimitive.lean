import EulerNonuniqueness.Section8.StreamFunction

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Convolution

namespace EulerNonuniqueness

theorem streamFunction_eq_integral_Iic (test : ℝ × Plane → Plane) (point : ℝ × Plane) :
    streamFunction test point = ∫ horizontal in Iic point.2.re, horizontalTestSlice test point horizontal := by
  have substitution := integral_sub_left_eq_self
    (fun horizontal => horizontalHeaviside horizontal * horizontalTestSlice test point (point.2.re - horizontal))
    volume point.2.re
  simp only [sub_sub_cancel] at substitution
  change (∫ horizontal, horizontalHeaviside horizontal * horizontalTestSlice test point (point.2.re - horizontal)) = _
  rw [← substitution]
  rw [← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun horizontal => by
    by_cases inside : horizontal ≤ point.2.re
    · have positive : 0 ≤ point.2.re - horizontal := sub_nonneg.mpr inside
      simp [horizontalHeaviside, positive, inside]
    · have negative : ¬0 ≤ point.2.re - horizontal := by linarith
      simp [horizontalHeaviside, negative, inside]

theorem hasDerivAt_integral_Iic {source : ℝ → ℝ} (continuous : Continuous source)
    (integrable : Integrable source) (point : ℝ) :
    HasDerivAt (fun endpoint => ∫ horizontal in Iic endpoint, source horizontal) (source point) point := by
  have equality : (fun endpoint => ∫ horizontal in Iic endpoint, source horizontal) =
      (fun endpoint => (∫ horizontal in Iic (0 : ℝ), source horizontal) + ∫ horizontal in (0 : ℝ)..endpoint, source horizontal) := by
    funext endpoint
    have identity := intervalIntegral.integral_Iic_sub_Iic
      (integrable.integrableOn (s := Iic (0 : ℝ))) (integrable.integrableOn (s := Iic endpoint))
    linarith
  rw [equality]
  exact (intervalIntegral.integral_hasDerivAt_right integrable.intervalIntegrable
    continuous.aestronglyMeasurable.stronglyMeasurableAtFilter continuous.continuousAt).const_add _

theorem integrable_horizontalTestSlice {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (point : ℝ × Plane) :
    Integrable (horizontalTestSlice test point) := by
  obtain ⟨radius, positive, supported⟩ := horizontalTestSlice_uniform_support compact
  have continuous : Continuous (horizontalTestSlice test point) :=
    (horizontalTestSlice_contDiff smooth).continuous.comp (continuous_const.prodMk continuous_id)
  exact continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) radius) (supported point))

theorem hasDerivAt_streamFunction_horizontal {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (time vertical horizontal : ℝ) :
    HasDerivAt (fun other : ℝ => streamFunction test (time, (other : ℂ) + (vertical : ℂ) * Complex.I))
      (test (time, (horizontal : ℂ) + (vertical : ℂ) * Complex.I)).im horizontal := by
  let point : ℝ × Plane := (time, (horizontal : ℂ) + (vertical : ℂ) * Complex.I)
  have continuous : Continuous (horizontalTestSlice test point) :=
    (horizontalTestSlice_contDiff smooth).continuous.comp (continuous_const.prodMk continuous_id)
  have derivative := hasDerivAt_integral_Iic continuous (integrable_horizontalTestSlice smooth compact point) horizontal
  have equality : (fun other : ℝ => streamFunction test (time, (other : ℂ) + (vertical : ℂ) * Complex.I)) =
      (fun other => ∫ coordinate in Iic other, horizontalTestSlice test point coordinate) := by
    funext other
    rw [streamFunction_eq_integral_Iic]
    simp only [horizontalTestSlice, point, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, zero_add, mul_one]
  rw [equality]
  simpa only [horizontalTestSlice, point, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using derivative

end EulerNonuniqueness
