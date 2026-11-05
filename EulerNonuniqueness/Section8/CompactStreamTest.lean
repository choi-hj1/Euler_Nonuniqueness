import EulerNonuniqueness.Section8.StreamSupport

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem hasCompactSupport_streamFunction {test : ℝ × Plane → Plane}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (divergence : ∀ point, spatialDivergence test point = 0) : HasCompactSupport (streamFunction test) := by
  obtain ⟨radius, positive, supported⟩ := vectorTest_coordinate_support compact
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × Plane) (2 * radius))
  intro point outside
  by_cases timeOutside : radius < |point.1|
  · exact streamFunction_eq_zero_of_time_or_vertical supported point (Or.inl timeOutside)
  by_cases verticalOutside : radius < |point.2.im|
  · exact streamFunction_eq_zero_of_time_or_vertical supported point (Or.inr verticalOutside)
  by_cases rightOutside : radius < point.2.re
  · exact streamFunction_eq_zero_of_horizontal_gt smooth compact divergence positive supported point rightOutside
  by_cases leftOutside : point.2.re < -radius
  · apply streamFunction_eq_zero_of_horizontal_lt (point := point) (radius := radius) ?_ leftOutside
    intro other horizontal horizontalOutside
    have bound : radius < |horizontal| := by simpa using horizontalOutside
    have zero := supported other.1 ((horizontal : ℂ) + (other.2.im : ℂ) * Complex.I) (Or.inr (Or.inl (by simpa using bound)))
    simp only [horizontalTestSlice, zero, Complex.zero_im]
  exfalso
  apply outside
  have timeBound : |point.1| ≤ radius := le_of_not_gt timeOutside
  have realBound : |point.2.re| ≤ radius := abs_le.mpr ⟨le_of_not_gt leftOutside, le_of_not_gt rightOutside⟩
  have imaginaryBound : |point.2.im| ≤ radius := le_of_not_gt verticalOutside
  have positionBound : ‖point.2‖ ≤ 2 * radius := (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)
  simpa only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using
    max_le (timeBound.trans (by linarith : radius ≤ 2 * radius)) positionBound

theorem scalarTestOn_streamFunction {horizon : ℝ} {test : ℝ × Plane → Plane}
    (admissible : VectorTestOn horizon test) : ScalarTestOn horizon (streamFunction test) := by
  refine ⟨contDiff_streamFunction admissible.1 admissible.2.1,
    hasCompactSupport_streamFunction admissible.1 admissible.2.1 admissible.2.2.2, ?_⟩
  intro time position outside
  rw [streamFunction_eq_integral_Iic]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun horizontal => by
    simp only [horizontalTestSlice, admissible.2.2.1 time _ outside, Complex.zero_im, Pi.zero_apply]

end EulerNonuniqueness
