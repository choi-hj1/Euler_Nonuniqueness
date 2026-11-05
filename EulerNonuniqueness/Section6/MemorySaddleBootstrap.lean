import EulerNonuniqueness.Section6.MemorySaddleRemainder
import EulerNonuniqueness.Section6.MemorySaddleBudget
import EulerNonuniqueness.Section6.UnstableBootstrap

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6.MemorySaddleSystem

theorem unstable_envelope {parameters : MemorySaddleParameters} {horizon scale cutoff : ℝ}
    (system : MemorySaddleSystem parameters horizon scale)
    (horizonNonnegative : 0 ≤ horizon) (scalePositive : 0 < scale) (cutoffNonnegative : 0 ≤ cutoff)
    (endpointBound : scale * Real.exp (parameters.growth * horizon) ≤ cutoff)
    (gap : parameters.directAmplitude + parameters.remainderBudget scale cutoff horizon < parameters.unstableAmplitude) :
    ∀ time ∈ Icc 0 horizon,
      |system.trajectory time| < scale * parameters.unstableAmplitude * Real.exp (parameters.growth * time) := by
  apply unstable_bootstrap_from_integral_remainder scalePositive horizonNonnegative
    (parameters.remainderBudget_nonnegative scalePositive.le cutoffNonnegative horizonNonnegative)
    gap system.forcingIntegrable system.equation system.directInputBound
  intro time inside envelope
  have localEndpoint : scale * Real.exp (parameters.growth * time) ≤ cutoff :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left inside.2 parameters.growthPositive.le)) scalePositive.le).trans endpointBound
  have estimate := (system.restrict inside).remainder_estimate_of_unstable_envelope
    inside.1 scalePositive.le localEndpoint envelope
  refine ⟨estimate.1, ?_⟩
  exact (estimate.2 time ⟨inside.1, le_rfl⟩).trans
    (mul_le_mul_of_nonneg_left (parameters.remainderBudget_mono scalePositive.le inside.2) scalePositive.le)

theorem quantitative_bounds {parameters : MemorySaddleParameters} {horizon scale cutoff : ℝ}
    (system : MemorySaddleSystem parameters horizon scale)
    (horizonNonnegative : 0 ≤ horizon) (scalePositive : 0 < scale) (cutoffNonnegative : 0 ≤ cutoff)
    (endpointBound : scale * Real.exp (parameters.growth * horizon) ≤ cutoff)
    (gap : parameters.directAmplitude + parameters.remainderBudget scale cutoff horizon < parameters.unstableAmplitude) :
    (∀ time ∈ Icc 0 horizon, |system.trajectory time| < scale * parameters.unstableAmplitude * Real.exp (parameters.growth * time)) ∧
      (∀ time ∈ Icc 0 horizon, system.history time ≤ scale * parameters.coarseHistory * Real.exp (parameters.growth * time)) ∧
      (∀ time ∈ Icc 0 horizon, system.stable time ≤ parameters.fastStable * parameters.smallness * scale * Real.exp (parameters.growth * time) +
        parameters.stableInitial * scale * Real.exp (parameters.slowRate * time)) ∧
      IntervalIntegrable (fun time => Real.exp (-parameters.growth * time) * system.remainder time) volume 0 horizon ∧
      ∀ time ∈ Icc 0 horizon,
        |∫ current in (0 : ℝ)..time, Real.exp (-parameters.growth * current) * system.remainder current| ≤
          scale * parameters.remainderBudget scale cutoff horizon := by
  have envelope := system.unstable_envelope horizonNonnegative scalePositive cutoffNonnegative endpointBound gap
  have weakEnvelope := fun time inside => (envelope time inside).le
  have bounds := system.bounds_of_unstable_envelope horizonNonnegative scalePositive.le weakEnvelope
  have remainder := system.remainder_estimate_of_unstable_envelope horizonNonnegative scalePositive.le endpointBound weakEnvelope
  refine ⟨envelope, bounds.2.1, bounds.2.2.2, remainder.1, ?_⟩
  intro time inside
  exact (remainder.2 time inside).trans
    (mul_le_mul_of_nonneg_left (parameters.remainderBudget_mono scalePositive.le inside.2) scalePositive.le)

end EulerNonuniqueness.Section6.MemorySaddleSystem
