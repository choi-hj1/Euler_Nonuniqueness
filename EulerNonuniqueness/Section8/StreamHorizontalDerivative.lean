import EulerNonuniqueness.Section8.StreamPrimitive

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem spatialDerivative_streamFunction_horizontal {test : ℝ × Plane → Plane}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (point : ℝ × Plane) :
    spatialDerivative (streamFunction test) point 1 = (test point).im := by
  have curve : HasDerivAt (fun other : ℝ => (point.1, (other : ℂ) + (point.2.im : ℂ) * Complex.I))
      (0, (1 : Plane)) point.2.re := by
    have realEmbedding := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt point.2.re (hasDerivAt_id point.2.re)
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (hasDerivAt_const point.2.re point.1).prodMk (realEmbedding.add_const ((point.2.im : ℂ) * Complex.I))
  have reconstructed : (point.1, (point.2.re : ℂ) + (point.2.im : ℂ) * Complex.I) = point := by
    exact Prod.ext rfl point.2.re_add_im
  have derivative := ((contDiff_streamFunction smooth compact).differentiable (by simp) point).hasFDerivAt
  have composition := derivative.comp_hasDerivAt_of_eq point.2.re curve reconstructed.symm
  have direct := hasDerivAt_streamFunction_horizontal smooth compact point.1 point.2.im point.2.re
  rw [reconstructed] at direct
  exact composition.unique direct

theorem streamFunction_eq_zero_of_horizontal_lt {test : ℝ × Plane → Plane}
    {radius : ℝ} (supported : ∀ point horizontal, horizontal ∉ Metric.closedBall (0 : ℝ) radius →
      horizontalTestSlice test point horizontal = 0) (point : ℝ × Plane)
    (outside : point.2.re < -radius) : streamFunction test point = 0 := by
  rw [streamFunction_eq_integral_Iic]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Iic] with horizontal inside
  apply supported point horizontal
  intro member
  have lower : -radius ≤ horizontal := by
    have bound : |horizontal| ≤ radius := by simpa using member
    exact (abs_le.mp bound).1
  exact (not_lt_of_ge (lower.trans inside)) outside

end EulerNonuniqueness
