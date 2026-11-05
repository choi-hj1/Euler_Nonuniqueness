import EulerNonuniqueness.Section1.PreResetAgeFromTiming
import EulerNonuniqueness.Section1.DelayedQuadraticCirculationSeedTail

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_timed_quadratic_circulation_seed_tail (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (alphaSmall : scales.alpha < 1) (ratioPower : 4 < scales.ratio ^ scales.alpha)
    {growth timingError : ℝ} (growthNonnegative : 0 ≤ growth)
    (timingErrorNonnegative : 0 ≤ timingError)
    (ratioSeparation : (growth + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1))
    (sectionTime : ℝ) (power : ℕ) {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count receiver : ℕ, ∀ selected : Finset ℕ,
      (∀ source ∈ selected, receiver + 2 ≤ source ∧ source ≤ count) →
      ∀ actualTime : ℕ → ℝ,
      let changed : Scales := {scales with frequency := frequency}
      |actualTime (receiver + 1) - changed.predictedTime sectionTime count (receiver + 1)| ≤
        timingError / changed.omega (receiver + 1) →
      (∀ source ∈ selected, |actualTime source - changed.predictedTime sectionTime count source| ≤
        timingError / changed.omega source) →
      (∀ source ∈ selected, actualTime source ≤ actualTime (receiver + 1)) →
      changed.omega receiver ^ power / (changed.omega receiver ^ 2 * changed.location receiver ^ 4) *
        (∑ source ∈ selected, (1 + (changed.location source)⁻¹) * changed.circulation source ^ 2 *
          (1 + changed.omega receiver * (actualTime (receiver + 1) - actualTime source)) *
          Real.exp (growth * changed.omega receiver * (actualTime (receiver + 1) - actualTime source))) ≤
        tolerance * changed.seed receiver / changed.ratio ^ 2 := by
  filter_upwards [scales.eventually_prereset_age_le_of_timing_close ratioBound alphaPositive alphaSmall
      sectionTime timingErrorNonnegative,
    scales.eventually_delayed_quadratic_circulation_seed_tail ratioBound alphaPositive alphaSmall ratioPower
      growthNonnegative (by norm_num : (0 : ℝ) ≤ 8) ratioSeparation power tolerancePositive]
    with frequency ages strengths
  intro count receiver selected selectedBounds actualTime
  dsimp only
  intro receiverTiming sourceTiming timeOrder
  exact strengths receiver selected (fun source member => (selectedBounds source member).1)
    (fun source => actualTime (receiver + 1) - actualTime source)
    (fun source member => ages count receiver source (selectedBounds source member).1
      (selectedBounds source member).2 actualTime receiverTiming (sourceTiming source member) (timeOrder source member))

end EulerNonuniqueness.Paper
