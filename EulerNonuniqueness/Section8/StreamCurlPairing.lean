import EulerNonuniqueness.Section8.CompactStreamTest
import EulerNonuniqueness.Section8.SmoothDivCurl

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem inner_vectorTest_eq_neg_stream_derivative {test : ℝ × Plane → Plane}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (divergence : ∀ point, spatialDivergence test point = 0) (point : ℝ × Plane) (velocity : Plane) :
    ⟪velocity, test point⟫_ℝ = -spatialDerivative (streamFunction test) point (Complex.I * velocity) := by
  have horizontal := spatialDerivative_streamFunction_horizontal smooth compact point
  have vertical := spatialDerivative_streamFunction_vertical smooth compact divergence point
  have linear := realLinearMap_apply_complex
    ((fderiv ℝ (streamFunction test) point).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) (Complex.I * velocity)
  change spatialDerivative (streamFunction test) point (Complex.I * velocity) =
    (Complex.I * velocity).re * spatialDerivative (streamFunction test) point 1 +
      (Complex.I * velocity).im * spatialDerivative (streamFunction test) point Complex.I at linear
  rw [linear, horizontal, vertical]
  rw [real_inner_eq_re_inner, RCLike.inner_apply]
  change (test point * (starRingEnd ℂ) velocity).re = _
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
  ring

theorem integral_biotSavart_vectorTest_eq_neg_vorticity_stream
    {vorticity : Vorticity} (integrable : Integrable vorticity) {radius : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {test : ℝ × Plane → Plane} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (divergence : ∀ point, spatialDivergence test point = 0) (time : ℝ) :
    Integrable (fun position => ⟪biotSavart vorticity position, test (time, position)⟫_ℝ) ∧
      (∫ position, ⟪biotSavart vorticity position, test (time, position)⟫_ℝ) =
        -(∫ position, vorticity position * streamFunction test (time, position)) := by
  have potentialSmooth := contDiff_streamFunction smooth compact
  have potentialCompact := hasCompactSupport_streamFunction smooth compact divergence
  have curl := curl_biotSavart_of_integrable_support integrable supported
    (contDiff_spatial_slice potentialSmooth time) (hasCompactSupport_spatial_slice potentialCompact time)
  have equality : (fun position => ⟪biotSavart vorticity position, test (time, position)⟫_ℝ) =
      (fun position => -fderiv ℝ (fun other => streamFunction test (time, other)) position
        (Complex.I * biotSavart vorticity position)) := by
    funext position
    rw [fderiv_spatial_slice potentialSmooth]
    exact inner_vectorTest_eq_neg_stream_derivative smooth compact divergence _ _
  rw [equality]
  exact ⟨curl.1.neg, by rw [integral_neg, curl.2]⟩

end EulerNonuniqueness
