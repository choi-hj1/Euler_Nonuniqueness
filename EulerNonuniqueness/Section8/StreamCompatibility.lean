import EulerNonuniqueness.Section8.DivCurlEnergy
import EulerNonuniqueness.Section8.StreamHorizontalDerivative

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem stream_vertical_derivative_of_compatibility {potential first second : Plane → ℝ}
    (potentialSmooth : ContDiff ℝ ∞ potential) (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (horizontal : ∀ position, fderiv ℝ potential position 1 = second position)
    (divergence : ∀ position, fderiv ℝ first position 1 + fderiv ℝ second position Complex.I = 0)
    (base : ∀ vertical : ℝ, ∃ horizontal : ℝ,
      fderiv ℝ potential ((horizontal : ℂ) + (vertical : ℂ) * Complex.I) Complex.I +
        first ((horizontal : ℂ) + (vertical : ℂ) * Complex.I) = 0) (position : Plane) :
    fderiv ℝ potential position Complex.I = -first position := by
  let defect := fun point => fderiv ℝ potential point Complex.I + first point
  have defectSmooth : ContDiff ℝ ∞ defect :=
    (contDiff_directionalDerivative potentialSmooth Complex.I).add firstSmooth
  have defectDerivative (point : Plane) : fderiv ℝ defect point 1 = 0 := by
    rw [fderiv_add ((contDiff_directionalDerivative potentialSmooth Complex.I).differentiable (by simp) point)
      (firstSmooth.differentiable (by simp) point), ContinuousLinearMap.add_apply,
      mixed_directionalDerivatives_commute potentialSmooth Complex.I 1 point,
      show (fun other => fderiv ℝ potential other 1) = second from funext horizontal]
    linarith [divergence point]
  let curve := fun other : ℝ => (other : ℂ) + (position.im : ℂ) * Complex.I
  have curveDerivative (other : ℝ) : HasDerivAt curve (1 : Plane) other := by
    have embedding := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt other (hasDerivAt_id other)
    exact embedding.add_const _
  have derivative (other : ℝ) : HasDerivAt (defect ∘ curve) 0 other := by
    have result := ((defectSmooth.differentiable (by simp) (curve other)).hasFDerivAt).comp_hasDerivAt other (curveDerivative other)
    simpa only [defectDerivative] using result
  obtain ⟨reference, zero⟩ := base position.im
  have constant := is_const_of_deriv_eq_zero (fun other => (derivative other).differentiableAt)
    (fun other => (derivative other).deriv) position.re reference
  have reconstruction : curve position.re = position := position.re_add_im
  simp only [Function.comp_apply, reconstruction, defect] at constant
  change fderiv ℝ potential position Complex.I + first position = _ at constant
  rw [zero] at constant
  linarith

end EulerNonuniqueness
