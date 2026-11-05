import EulerNonuniqueness.Section6.MemorySaddleData
import EulerNonuniqueness.Section6.MemoryCoarseBounds
import EulerNonuniqueness.Section6.MemoryRefinedBounds

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6.MemorySaddleSystem

theorem bounds_of_unstable_envelope {parameters : MemorySaddleParameters} {horizon scale : ℝ}
    (system : MemorySaddleSystem parameters horizon scale)
    (horizonNonnegative : 0 ≤ horizon) (scaleNonnegative : 0 ≤ scale)
    (unstableEnvelope : ∀ time ∈ Icc 0 horizon,
      |system.trajectory time| ≤ scale * parameters.unstableAmplitude * Real.exp (parameters.growth * time)) :
    (∀ time ∈ Icc 0 horizon, system.stable time ≤ scale * parameters.coarseStable * Real.exp (parameters.growth * time)) ∧
    (∀ time ∈ Icc 0 horizon, system.history time ≤ scale * parameters.coarseHistory * Real.exp (parameters.growth * time)) ∧
    (∀ time ∈ Icc 0 horizon, system.returned time ≤
      scale * parameters.smallness * (parameters.unstableAmplitude + parameters.coarseStable + parameters.coarseHistory) * Real.exp (parameters.growth * time)) ∧
    (∀ time ∈ Icc 0 horizon, system.stable time ≤
      parameters.fastStable * parameters.smallness * scale * Real.exp (parameters.growth * time) +
        parameters.stableInitial * scale * Real.exp (parameters.slowRate * time)) := by
  have multiplierNonnegative := parameters.multiplierNonnegative
  have unstableNonnegative := parameters.unstableNonnegative
  have stableInitialNonnegative := parameters.stableNonnegative
  have historyInitialNonnegative := parameters.historyNonnegative
  have driveNonnegative := parameters.driveNonnegative
  have smallnessNonnegative := parameters.smallnessNonnegative
  have slowGrowth : parameters.slowRate ≤ parameters.growth := by
    nlinarith [parameters.slowGrowth, parameters.growthPositive]
  have driveEnvelope (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      system.drive time ≤ (scale * parameters.driveAmplitude) * Real.exp (parameters.growth * time) :=
    (system.driveBound time inside).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right slowGrowth inside.1)) (mul_nonneg scaleNonnegative driveNonnegative))
  obtain ⟨stableBound, historyBound, stableBoundNonnegative, historyBoundNonnegative,
      stableEnvelope, historyEnvelope, returnedEnvelope, stableNumeric, historyNumeric⟩ :=
    memory_coarse_bounds horizonNonnegative parameters.rate_lt_growth multiplierNonnegative parameters.gainNonnegative
      smallnessNonnegative parameters.chartNonnegative (by positivity) (by positivity) (by positivity) (by positivity)
      parameters.gainBound
      ((by norm_num : (0 : ℝ) ≤ 3 / 4).trans parameters.diagonal_bounds.1)
      ((by norm_num : (0 : ℝ) ≤ 3 / 4).trans parameters.diagonal_bounds.2.1)
      parameters.determinant_positive system.trajectoryContinuous.abs system.stableContinuous system.historyContinuous
      system.driveContinuous system.returnedContinuous system.stableNonnegative system.historyNonnegative
      unstableEnvelope driveEnvelope system.localNonnegative system.kernelContinuous system.kernelNonnegative
      system.kernelBound system.returnedEquation system.stableInequality system.historyInequality
  have stableScaled : stableBound ≤ scale * parameters.coarseStable := by
    convert stableNumeric using 1 <;> dsimp only [MemorySaddleParameters.coarseStable, MemorySaddleParameters.determinant] <;> ring
  have historyScaled : historyBound ≤ scale * parameters.coarseHistory := by
    convert historyNumeric using 1 <;> dsimp only [MemorySaddleParameters.coarseHistory, MemorySaddleParameters.determinant] <;> ring
  have stableCoarse (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      system.stable time ≤ scale * parameters.coarseStable * Real.exp (parameters.growth * time) :=
    (stableEnvelope time inside).trans (mul_le_mul_of_nonneg_right stableScaled (Real.exp_pos _).le)
  have historyCoarse (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      system.history time ≤ scale * parameters.coarseHistory * Real.exp (parameters.growth * time) :=
    (historyEnvelope time inside).trans (mul_le_mul_of_nonneg_right historyScaled (Real.exp_pos _).le)
  have returnedCoarse (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      system.returned time ≤ parameters.smallness *
        (scale * parameters.unstableAmplitude + scale * parameters.coarseStable + scale * parameters.coarseHistory) * Real.exp (parameters.growth * time) := by
    exact (returnedEnvelope time inside).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add_left stableScaled _) historyScaled) smallnessNonnegative)
      (Real.exp_pos _).le)
  have returnedScaled (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      system.returned time ≤ scale * parameters.smallness *
        (parameters.unstableAmplitude + parameters.coarseStable + parameters.coarseHistory) * Real.exp (parameters.growth * time) := by
    convert returnedCoarse time inside using 1 <;> ring
  have stableConstantNonnegative := parameters.constants_nonnegative.1
  have historyConstantNonnegative := parameters.constants_nonnegative.2.1
  have refined := memory_refined_stable_bound horizonNonnegative multiplierNonnegative smallnessNonnegative
    parameters.chartNonnegative (by positivity) (by positivity) (by positivity) (by positivity)
    parameters.effective_lt_growth parameters.slowRateBound system.trajectoryContinuous.abs system.stableContinuous
    system.historyContinuous system.returnedContinuous unstableEnvelope historyCoarse returnedCoarse system.stableInequality
  refine ⟨stableCoarse, historyCoarse, returnedScaled, ?_⟩
  intro time inside
  convert refined time inside using 1 <;> dsimp only [MemorySaddleParameters.fastStable] <;> ring

end EulerNonuniqueness.Section6.MemorySaddleSystem
