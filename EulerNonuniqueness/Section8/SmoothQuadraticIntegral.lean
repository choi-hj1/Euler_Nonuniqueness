import EulerNonuniqueness.Section8.SmoothQuadraticIdentity

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

def transportQuadratic (first second potential : Plane → ℝ) (position : Plane) : ℝ :=
  (first position ^ 2 - second position ^ 2) * fderiv ℝ (fun other => fderiv ℝ potential other 1) position Complex.I +
    first position * second position *
      (fderiv ℝ (fun other => fderiv ℝ potential other Complex.I) position Complex.I -
        fderiv ℝ (fun other => fderiv ℝ potential other 1) position 1)

theorem integral_smooth_transport_quadratic {first second potential : Plane → ℝ}
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second)
    (potentialSmooth : ContDiff ℝ ∞ potential) (compact : HasCompactSupport potential)
    (divergence : ∀ position, fderiv ℝ first position 1 + fderiv ℝ second position Complex.I = 0) :
    (∫ position, -second position * fderiv ℝ (fun other => first other * fderiv ℝ potential other 1 +
      second other * fderiv ℝ potential other Complex.I) position 1 +
      first position * fderiv ℝ (fun other => first other * fderiv ℝ potential other 1 +
        second other * fderiv ℝ potential other Complex.I) position Complex.I) =
      ∫ position, transportQuadratic first second potential position := by
  let energy := fun position => first position * first position + second position * second position
  have energySmooth : ContDiff ℝ ∞ energy := (firstSmooth.mul firstSmooth).add (secondSmooth.mul secondSmooth)
  have firstDerivativeSmooth := contDiff_directionalDerivative potentialSmooth 1
  have secondDerivativeSmooth := contDiff_directionalDerivative potentialSmooth Complex.I
  have firstCrossIntegrable : Integrable (fun position => fderiv ℝ potential position 1 * fderiv ℝ energy position Complex.I) :=
    (firstDerivativeSmooth.continuous.mul (contDiff_directionalDerivative energySmooth Complex.I).continuous).integrable_of_hasCompactSupport
      (compact.fderiv_apply ℝ 1).mul_right
  have secondCrossIntegrable : Integrable (fun position => fderiv ℝ potential position Complex.I * fderiv ℝ energy position 1) :=
    (secondDerivativeSmooth.continuous.mul (contDiff_directionalDerivative energySmooth 1).continuous).integrable_of_hasCompactSupport
      (compact.fderiv_apply ℝ Complex.I).mul_right
  have mixedSmooth := contDiff_directionalDerivative firstDerivativeSmooth Complex.I
  have verticalSmooth := contDiff_directionalDerivative secondDerivativeSmooth Complex.I
  have horizontalSmooth := contDiff_directionalDerivative firstDerivativeSmooth 1
  have mixedCompact := (compact.fderiv_apply ℝ 1).fderiv_apply ℝ Complex.I
  have verticalCompact := (compact.fderiv_apply ℝ Complex.I).fderiv_apply ℝ Complex.I
  have horizontalCompact := (compact.fderiv_apply ℝ 1).fderiv_apply ℝ 1
  have quadraticContinuous : Continuous (transportQuadratic first second potential) :=
    (((firstSmooth.continuous.pow 2).sub (secondSmooth.continuous.pow 2)).mul mixedSmooth.continuous).add
      ((firstSmooth.continuous.mul secondSmooth.continuous).mul (verticalSmooth.continuous.sub horizontalSmooth.continuous))
  have quadraticCompact : HasCompactSupport (transportQuadratic first second potential) :=
    mixedCompact.mul_left.add (verticalCompact.comp₂_left horizontalCompact (m := fun first second : ℝ => first - second) (by simp)).mul_left
  have quadraticIntegrable := quadraticContinuous.integrable_of_hasCompactSupport quadraticCompact (μ := volume)
  have crossIntegral : (∫ position, (fderiv ℝ potential position 1 * fderiv ℝ energy position Complex.I -
      fderiv ℝ potential position Complex.I * fderiv ℝ energy position 1) / 2) = 0 := by
    rw [integral_div, integral_sub firstCrossIntegrable secondCrossIntegrable,
      integral_cross_directionalDerivatives potentialSmooth compact energySmooth 1 Complex.I, sub_self, zero_div]
  have identity : (fun position => -second position * fderiv ℝ (fun other => first other * fderiv ℝ potential other 1 +
      second other * fderiv ℝ potential other Complex.I) position 1 +
      first position * fderiv ℝ (fun other => first other * fderiv ℝ potential other 1 +
        second other * fderiv ℝ potential other Complex.I) position Complex.I) =
      (fun position => (fderiv ℝ potential position 1 * fderiv ℝ energy position Complex.I -
        fderiv ℝ potential position Complex.I * fderiv ℝ energy position 1) / 2 + transportQuadratic first second potential position) := by
    funext position
    simpa only [transportQuadratic, energy, add_assoc] using
      smooth_transport_quadratic_pointwise firstSmooth secondSmooth potentialSmooth divergence position
  have crossIntegrable : Integrable (fun position => (fderiv ℝ potential position 1 * fderiv ℝ energy position Complex.I -
      fderiv ℝ potential position Complex.I * fderiv ℝ energy position 1) / 2) :=
    (firstCrossIntegrable.sub secondCrossIntegrable).div_const 2
  rw [identity, integral_add crossIntegrable quadraticIntegrable, crossIntegral, zero_add]

end EulerNonuniqueness
