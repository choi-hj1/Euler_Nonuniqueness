import EulerNonuniqueness.Section8.SmoothStreamMomentum
import EulerNonuniqueness.Section8.MollifiedTransportPairingLimit
import EulerNonuniqueness.Section8.MollifiedQuadraticLimit

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem spatialTest_operator_properties {test : ℝ × Plane → Plane}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (time : ℝ) :
    Continuous (fun position => (fderiv ℝ test (time, position)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) ∧
      HasCompactSupport (fun position => (fderiv ℝ test (time, position)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) := by
  constructor
  · exact ((smooth.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  · apply HasCompactSupport.of_support_subset_isCompact ((compact.fderiv ℝ).isCompact.image continuous_snd)
    intro position nonzero
    refine ⟨(time, position), subset_tsupport _ ?_, rfl⟩
    intro zero
    exact nonzero (by simp only [zero, ContinuousLinearMap.zero_comp])

theorem integral_vorticity_stream_transport_eq_neg_momentum {vorticity : Vorticity} {radius : ℝ}
    (nonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (divergence : ∀ point, spatialDivergence test point = 0) (time : ℝ) :
    (∫ position, vorticity position * spatialDerivative (streamFunction test) (time, position) (biotSavart vorticity position)) =
      -(∫ position, ⟪biotSavart vorticity position, spatialDerivative test (time, position) (biotSavart vorticity position)⟫_ℝ) := by
  have integrable : Integrable vorticity := memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have potentialSmooth := contDiff_streamFunction smooth compact
  have potentialCompact := hasCompactSupport_streamFunction smooth compact divergence
  have leftLimit := tendsto_integral_mollified_vorticity_transport nonnegative membership supported
    (contDiff_spatial_slice potentialSmooth time) (hasCompactSupport_spatial_slice potentialCompact time)
  simp_rw [fderiv_spatial_slice potentialSmooth] at leftLimit
  obtain ⟨operatorContinuous, operatorCompact⟩ := spatialTest_operator_properties smooth compact time
  have rightLimit := (tendsto_integral_biotSavart_mollification_quadratic nonnegative membership supported
    operatorContinuous operatorCompact).neg
  have sameSequence (index : ℕ) := integral_smooth_vorticity_stream_transport_eq_neg_momentum
    (contDiff_mollification integrable index) (hasCompactSupport_mollification supported index) smooth compact divergence time
  exact tendsto_nhds_unique leftLimit (rightLimit.congr fun index => (sameSequence index).symm)

end EulerNonuniqueness
