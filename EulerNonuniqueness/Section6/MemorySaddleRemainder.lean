import EulerNonuniqueness.Section6.ScaledMemoryBounds
import EulerNonuniqueness.Section6.SaddleRemainderBound

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6.MemorySaddleSystem

theorem remainder_estimate_of_unstable_envelope {parameters : MemorySaddleParameters} {horizon scale cutoff : ℝ}
    (system : MemorySaddleSystem parameters horizon scale)
    (horizonNonnegative : 0 ≤ horizon) (scaleNonnegative : 0 ≤ scale)
    (endpointBound : scale * Real.exp (parameters.growth * horizon) ≤ cutoff)
    (unstableEnvelope : ∀ time ∈ Icc 0 horizon,
      |system.trajectory time| ≤ scale * parameters.unstableAmplitude * Real.exp (parameters.growth * time)) :
    IntervalIntegrable (fun time => Real.exp (-parameters.growth * time) * system.remainder time) volume 0 horizon ∧
      ∀ time ∈ Icc 0 horizon,
        |∫ current in (0 : ℝ)..time, Real.exp (-parameters.growth * current) * system.remainder current| ≤
          scale * parameters.remainderBudget scale cutoff time := by
  obtain ⟨stableCoarse, historyCoarse, returnedCoarse, stableRefined⟩ :=
    system.bounds_of_unstable_envelope horizonNonnegative scaleNonnegative unstableEnvelope
  have multiplierNonnegative := parameters.multiplierNonnegative
  have smallnessNonnegative := parameters.smallnessNonnegative
  have unstableNonnegative := parameters.unstableNonnegative
  have stableConstantNonnegative := parameters.constants_nonnegative.1
  have historyConstantNonnegative := parameters.constants_nonnegative.2.1
  have fastNonnegative := parameters.constants_nonnegative.2.2.1
  have remainderMultiplierNonnegative := parameters.constants_nonnegative.2.2.2
  have stableInitialNonnegative := parameters.stableNonnegative
  have driveAmplitudeNonnegative := parameters.driveNonnegative
  have nonlinearBound (time : ℝ) (inside : time ∈ Icc 0 horizon) : |system.remainder time| ≤
      parameters.remainderMultiplier * parameters.smallness * scale * Real.exp (parameters.growth * time) +
        parameters.remainderMultiplier * scale * Real.exp (parameters.growth * time) * (system.stable time + system.drive time) := by
    have totalBound : |system.trajectory time| + system.stable time ≤
        scale * (parameters.unstableAmplitude + parameters.coarseStable) * Real.exp (parameters.growth * time) := by
      convert add_le_add (unstableEnvelope time inside) (stableCoarse time inside) using 1 <;> ring
    have sumNonnegative : 0 ≤ system.stable time + system.drive time :=
      add_nonneg (system.stableNonnegative time inside) (system.driveNonnegative time inside)
    have estimate := (system.remainderBound time inside).trans (add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left totalBound smallnessNonnegative)
        (mul_le_mul_of_nonneg_right totalBound sumNonnegative))
        (mul_le_mul_of_nonneg_left (historyCoarse time inside) smallnessNonnegative)) multiplierNonnegative)
      (returnedCoarse time inside))
    let constantCoefficient := parameters.multiplier * (parameters.unstableAmplitude + parameters.coarseStable) +
      parameters.multiplier * parameters.coarseHistory + (parameters.unstableAmplitude + parameters.coarseStable + parameters.coarseHistory)
    let quadraticCoefficient := parameters.multiplier * (parameters.unstableAmplitude + parameters.coarseStable)
    have constantNonnegative : 0 ≤ constantCoefficient := by dsimp only [constantCoefficient]; positivity
    have quadraticNonnegative : 0 ≤ quadraticCoefficient := by dsimp only [quadraticCoefficient]; positivity
    have constantBound : constantCoefficient ≤ parameters.remainderMultiplier := by
      change constantCoefficient ≤ constantCoefficient + quadraticCoefficient
      exact le_add_of_nonneg_right quadraticNonnegative
    have quadraticBound : quadraticCoefficient ≤ parameters.remainderMultiplier := by
      change quadraticCoefficient ≤ constantCoefficient + quadraticCoefficient
      exact le_add_of_nonneg_left constantNonnegative
    have enlarged := add_le_add
      (mul_le_mul_of_nonneg_right constantBound
        (by positivity : 0 ≤ parameters.smallness * scale * Real.exp (parameters.growth * time)))
      (mul_le_mul_of_nonneg_right quadraticBound
        (by positivity : 0 ≤ scale * Real.exp (parameters.growth * time) * (system.stable time + system.drive time)))
    apply estimate.trans
    convert enlarged using 1 <;> dsimp only [constantCoefficient, quadraticCoefficient] <;> ring
  have driveBound (time : ℝ) (inside : time ∈ Icc 0 horizon) : system.drive time ≤
      parameters.driveAmplitude * scale * Real.exp (parameters.slowRate * time) := by
    simpa only [mul_comm parameters.driveAmplitude scale] using system.driveBound time inside
  have bounded := saddle_remainder_integral_bound parameters.growthPositive parameters.slowPositive
    scaleNonnegative smallnessNonnegative remainderMultiplierNonnegative fastNonnegative
    stableInitialNonnegative driveAmplitudeNonnegative horizonNonnegative endpointBound
    system.remainderMeasurable stableRefined driveBound nonlinearBound
  simpa only [MemorySaddleParameters.remainderBudget] using bounded

end EulerNonuniqueness.Section6.MemorySaddleSystem
