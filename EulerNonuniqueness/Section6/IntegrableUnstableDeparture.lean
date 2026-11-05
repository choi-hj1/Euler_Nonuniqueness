import EulerNonuniqueness.Section6.UnstableDeparture

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem unstable_departure_of_integrable_inputs {trajectory forcing remainder : ℝ → ℝ}
    {rate scale coefficient threshold earlyBound earlyTime horizon : ℝ}
    (forcingIntegrable : IntervalIntegrable (fun current => Real.exp (-rate * current) * forcing current) volume 0 horizon)
    (remainderIntegrable : IntervalIntegrable (fun current => Real.exp (-rate * current) * remainder current) volume 0 horizon)
    (equation : ∀ current ∈ Icc 0 horizon, HasDerivAt trajectory
      (rate * trajectory current + scale * forcing current + remainder current) current)
    (ratePositive : 0 < rate) (scalePositive : 0 < scale) (coefficientPositive : 0 < coefficient)
    (thresholdPositive : 0 < threshold) (earlyBoundNonnegative : 0 ≤ earlyBound)
    (earlyTimeNonnegative : 0 ≤ earlyTime) (earlyTimeBound : earlyTime ≤ horizon)
    (earlySmall : scale * earlyBound * Real.exp (rate * earlyTime) < threshold)
    (finalLarge : 4 * threshold ≤ scale * coefficient * Real.exp (rate * horizon))
    (earlyInput : ∀ time ∈ Icc 0 earlyTime,
      |trajectory 0 + scale * (∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * forcing current)| +
        |∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * remainder current| ≤ scale * earlyBound)
    (lateInput : ∀ time ∈ Icc earlyTime horizon,
      |trajectory 0 + scale * (∫ current in (0 : ℝ)..time,
        Real.exp (-rate * current) * forcing current) - scale * coefficient| ≤ scale * coefficient / 4)
    (lateRemainder : ∀ time ∈ Icc earlyTime horizon,
      |∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * remainder current| ≤ scale * coefficient / 4) :
    (∀ time ∈ Icc 0 horizon, -threshold < trajectory time) ∧
      ∃ time ∈ Icc 0 horizon, earlyTime < time ∧ trajectory time = threshold := by
  apply unstable_departure_of_weighted_coefficients
    (fun time inside => (equation time inside).continuousAt.continuousWithinAt)
    ratePositive scalePositive coefficientPositive thresholdPositive earlyBoundNonnegative
    earlyTimeNonnegative earlyTimeBound earlySmall finalLarge
  · intro time inside
    rw [integrable_unstable_duhamel forcingIntegrable remainderIntegrable equation
      ⟨inside.1, inside.2.trans earlyTimeBound⟩]
    exact (abs_add _ _).trans (earlyInput time inside)
  · intro time inside
    have bound := integrable_unstable_coefficient_error (coefficient := coefficient)
      (tail := coefficient / 4) (error := coefficient / 4)
      forcingIntegrable remainderIntegrable equation ⟨earlyTimeNonnegative.trans inside.1, inside.2⟩
      (by convert lateInput time inside using 1 <;> ring)
      (by convert lateRemainder time inside using 1 <;> ring)
    convert bound using 1 <;> ring

end EulerNonuniqueness.Section6
