import EulerNonuniqueness.Section8.SmoothDivCurl

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem smooth_transport_quadratic_pointwise {first second potential : Plane → ℝ}
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (potentialSmooth : ContDiff ℝ ∞ potential)
    (divergence : ∀ position, fderiv ℝ first position 1 + fderiv ℝ second position Complex.I = 0)
    (position : Plane) :
    -second position * fderiv ℝ (fun other => first other * fderiv ℝ potential other 1 +
      second other * fderiv ℝ potential other Complex.I) position 1 +
      first position * fderiv ℝ (fun other => first other * fderiv ℝ potential other 1 +
        second other * fderiv ℝ potential other Complex.I) position Complex.I =
    (fderiv ℝ potential position 1 * fderiv ℝ (fun other => first other * first other + second other * second other) position Complex.I -
      fderiv ℝ potential position Complex.I * fderiv ℝ (fun other => first other * first other + second other * second other) position 1) / 2 +
      (first position ^ 2 - second position ^ 2) * fderiv ℝ (fun other => fderiv ℝ potential other 1) position Complex.I +
      first position * second position *
        (fderiv ℝ (fun other => fderiv ℝ potential other Complex.I) position Complex.I -
          fderiv ℝ (fun other => fderiv ℝ potential other 1) position 1) := by
  have firstDifferentiable := firstSmooth.differentiable (by simp) position
  have secondDifferentiable := secondSmooth.differentiable (by simp) position
  have horizontalDifferentiable := (contDiff_directionalDerivative potentialSmooth 1).differentiable (by simp) position
  have verticalDifferentiable := (contDiff_directionalDerivative potentialSmooth Complex.I).differentiable (by simp) position
  simp only [fderiv_add (firstDifferentiable.mul horizontalDifferentiable) (secondDifferentiable.mul verticalDifferentiable),
    fderiv_mul firstDifferentiable horizontalDifferentiable, fderiv_mul secondDifferentiable verticalDifferentiable,
    fderiv_add (firstDifferentiable.mul firstDifferentiable) (secondDifferentiable.mul secondDifferentiable),
    fderiv_mul firstDifferentiable firstDifferentiable, fderiv_mul secondDifferentiable secondDifferentiable,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [mixed_directionalDerivatives_commute potentialSmooth Complex.I 1 position]
  have zero := divergence position
  linear_combination (first position * fderiv ℝ potential position Complex.I - second position * fderiv ℝ potential position 1) * zero

end EulerNonuniqueness
