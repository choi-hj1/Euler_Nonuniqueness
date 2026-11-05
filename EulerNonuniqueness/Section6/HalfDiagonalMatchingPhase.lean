import EulerNonuniqueness.Section6.HalfDiagonalCanonicalProfile
import EulerNonuniqueness.Section6.NormalizedOrbitIncomingDynamics

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem halfDiagonalMatchingRotation_eq_phase_difference
    {positive referencePositive : ℂ} {phase referencePhase : ℝ}
    (positiveNonzero : positive ≠ 0) (referenceNonzero : referencePositive ≠ 0)
    (positivePolar : positive = (‖positive‖ : ℂ) * Complex.exp (Complex.I * (phase : ℂ)))
    (referencePolar : referencePositive = (‖referencePositive‖ : ℂ) *
      Complex.exp (Complex.I * (referencePhase : ℂ))) :
    halfDiagonalMatchingRotation positive referencePositive =
      Complex.exp (Complex.I * ((phase - referencePhase : ℝ) : ℂ)) := by
  have positivePhase : positive / (‖positive‖ : ℂ) = Complex.exp (Complex.I * (phase : ℂ)) := by
    nth_rw 1 [positivePolar]
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr positiveNonzero))
  have referencePhaseIdentity : referencePositive / (‖referencePositive‖ : ℂ) =
      Complex.exp (Complex.I * (referencePhase : ℂ)) := by
    nth_rw 1 [referencePolar]
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr referenceNonzero))
  rw [halfDiagonalMatchingRotation, positivePhase, referencePhaseIdentity, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

theorem normalizedSeparatingOrbit_matchingRotation_eq_phase_difference
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (incomingTime : ℝ) {positive : ℂ} {phase : ℝ}
    (positiveNonzero : positive ≠ 0)
    (positivePolar : positive = (‖positive‖ : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) :
    halfDiagonalMatchingRotation positive (orbit.positive incomingTime) =
      Complex.exp (Complex.I * ((phase - orbit.phase incomingTime : ℝ) : ℂ)) := by
  have difference := (normalized.2.1 incomingTime).1
  have referenceNonzero : orbit.positive incomingTime ≠ 0 := by
    intro zero
    rw [zero, norm_zero] at difference
    nlinarith [sq_nonneg ‖orbit.negative incomingTime‖]
  exact halfDiagonalMatchingRotation_eq_phase_difference positiveNonzero referenceNonzero positivePolar
    (normalized.2.1 incomingTime).2.1

theorem normalizedSeparatingOrbit_eventually_phase_target
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    {accuracy : ℝ} (accuracyPositive : 0 < accuracy) :
    ∀ᶠ incomingTime : ℝ in atBot, |orbit.phase incomingTime + incomingTime| < accuracy := by
  have phaseLimit := normalized.2.2.2.2.2.2.1
  have actual := phaseLimit.abs.eventually (eventually_lt_nhds (by simpa using accuracyPositive : |(0 : ℝ)| < accuracy))
  exact actual

end EulerNonuniqueness.Section6
