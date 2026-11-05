import EulerNonuniqueness.Section8.StreamQuadraticPairing
import EulerNonuniqueness.Section8.SmoothVorticityQuadratic

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem integral_smooth_vorticity_stream_transport_eq_neg_momentum {vorticity : Vorticity}
    (sourceSmooth : ContDiff ℝ ∞ vorticity) (sourceCompact : HasCompactSupport vorticity)
    {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (divergence : ∀ point, spatialDivergence test point = 0) (time : ℝ) :
    (∫ position, vorticity position * spatialDerivative (streamFunction test) (time, position) (biotSavart vorticity position)) =
      -(∫ position, ⟪biotSavart vorticity position, spatialDerivative test (time, position) (biotSavart vorticity position)⟫_ℝ) := by
  have potentialSmooth := contDiff_streamFunction smooth compact
  have potentialCompact := hasCompactSupport_streamFunction smooth compact divergence
  have identity := integral_smooth_vorticity_transport_eq_quadratic sourceSmooth sourceCompact
    (contDiff_spatial_slice potentialSmooth time) (hasCompactSupport_spatial_slice potentialCompact time)
  simp_rw [fderiv_spatial_slice potentialSmooth] at identity
  rw [identity, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun position => by
    have equality := inner_vectorTest_advection_eq_neg_transportQuadratic smooth compact divergence time position (biotSavart vorticity position)
    dsimp only [transportQuadratic] at equality ⊢
    linarith

end EulerNonuniqueness
