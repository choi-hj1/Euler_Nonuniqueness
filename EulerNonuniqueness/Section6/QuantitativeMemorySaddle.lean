import EulerNonuniqueness.Section6.StoppedMemorySaddle

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

namespace MemorySaddleParameters

def departureCutoff (_parameters : MemorySaddleParameters) (coefficient threshold : ℝ) : ℝ :=
  4 * threshold / coefficient

def departureHorizon (parameters : MemorySaddleParameters) (scale coefficient threshold : ℝ) : ℝ :=
  Real.log (parameters.departureCutoff coefficient threshold / scale) / parameters.growth

def departureBudget (parameters : MemorySaddleParameters) (scale coefficient threshold : ℝ) : ℝ :=
  parameters.remainderMultiplier * parameters.smallness * parameters.departureHorizon scale coefficient threshold +
    parameters.remainderMultiplier * parameters.fastStable * parameters.smallness * parameters.departureCutoff coefficient threshold / parameters.growth +
    (parameters.remainderMultiplier * (parameters.stableInitial + parameters.driveAmplitude) / parameters.slowRate) *
      (parameters.departureCutoff coefficient threshold) ^ (parameters.slowRate / parameters.growth) * scale ^ (3 / 4 : ℝ)

end MemorySaddleParameters

namespace MemorySaddleSystem

theorem quantitative_memory_saddle {parameters : MemorySaddleParameters}
    {stopped scale coefficient threshold earlyTime tailAmplitude : ℝ}
    (system : MemorySaddleSystem parameters stopped scale)
    (stoppedNonnegative : 0 ≤ stopped)
    (stoppedBound : stopped ≤ parameters.departureHorizon scale coefficient threshold)
    (scalePositive : 0 < scale) (scaleBound : scale ≤ 1)
    (coefficientPositive : 0 < coefficient) (thresholdPositive : 0 < threshold)
    (tailNonnegative : 0 ≤ tailAmplitude) (earlyNonnegative : 0 ≤ earlyTime)
    (earlyBound : earlyTime ≤ parameters.departureHorizon scale coefficient threshold)
    (gap : parameters.directAmplitude + parameters.departureBudget scale coefficient threshold < parameters.unstableAmplitude)
    (remainderSmall : parameters.departureBudget scale coefficient threshold ≤ coefficient / 4)
    (earlySmall : scale * parameters.unstableAmplitude * Real.exp (parameters.growth * earlyTime) < threshold)
    (earlyTailSmall : tailAmplitude * Real.exp (-(3 * parameters.growth / 4) * earlyTime) ≤ coefficient / 4)
    (directTail : ∀ time ∈ Icc earlyTime stopped,
      |system.trajectory 0 + scale * (∫ current in (0 : ℝ)..time,
        Real.exp (-parameters.growth * current) * system.forcing current) - scale * coefficient| ≤
          scale * (tailAmplitude * Real.exp (-(3 * parameters.growth / 4) * time)))
    (stopUpper : system.trajectory stopped ≤ threshold)
    (stopCases : system.trajectory stopped = threshold ∨ system.trajectory stopped = -threshold ∨
      stopped = parameters.departureHorizon scale coefficient threshold) :
    (∀ time ∈ Icc 0 stopped, -threshold < system.trajectory time) ∧
      system.trajectory stopped = threshold ∧ earlyTime < stopped ∧
      |stopped - Real.log (threshold / (scale * coefficient)) / parameters.growth| ≤
        2 * (parameters.departureBudget scale coefficient threshold +
          tailAmplitude * (parameters.unstableAmplitude / threshold) ^ (3 / 4 : ℝ) * scale ^ (3 / 4 : ℝ)) /
            (parameters.growth * coefficient) ∧
      system.stable stopped ≤ parameters.fastStable * parameters.smallness * parameters.departureCutoff coefficient threshold +
        parameters.stableInitial * (parameters.departureCutoff coefficient threshold) ^ (parameters.slowRate / parameters.growth) *
          scale ^ (3 / 4 : ℝ) := by
  have cutoffPositive : 0 < parameters.departureCutoff coefficient threshold := by
    unfold MemorySaddleParameters.departureCutoff
    positivity
  have endpoint : scale * Real.exp (parameters.growth * parameters.departureHorizon scale coefficient threshold) =
      parameters.departureCutoff coefficient threshold :=
    delay_exponential_endpoint parameters.growthPositive.ne' scalePositive cutoffPositive
  have finalLarge : 4 * threshold ≤ scale * coefficient *
      Real.exp (parameters.growth * parameters.departureHorizon scale coefficient threshold) := by
    have identity : 4 * threshold = coefficient * parameters.departureCutoff coefficient threshold := by
      unfold MemorySaddleParameters.departureCutoff
      field_simp
    rw [← endpoint] at identity
    nlinarith
  have budgetBound : parameters.remainderBudget scale (parameters.departureCutoff coefficient threshold)
      (parameters.departureHorizon scale coefficient threshold) ≤ parameters.departureBudget scale coefficient threshold :=
    parameters.remainderBudget_at_delay_le scalePositive scaleBound cutoffPositive
  have actualGap : parameters.directAmplitude + parameters.remainderBudget scale
      (parameters.departureCutoff coefficient threshold) (parameters.departureHorizon scale coefficient threshold) < parameters.unstableAmplitude := by
    linarith
  have actualSmall : parameters.remainderBudget scale (parameters.departureCutoff coefficient threshold)
      (parameters.departureHorizon scale coefficient threshold) ≤ coefficient / 4 := budgetBound.trans remainderSmall
  obtain ⟨excluded, hit, afterEarly, delayBound, stableBound⟩ :=
    system.stopped_quantitative_departure stoppedNonnegative stoppedBound scalePositive cutoffPositive.le
      coefficientPositive thresholdPositive tailNonnegative earlyNonnegative earlyBound endpoint.le
      actualGap actualSmall earlySmall earlyTailSmall finalLarge directTail stopUpper stopCases
  have fullDelayBound : |stopped - Real.log (threshold / (scale * coefficient)) / parameters.growth| ≤
      2 * (parameters.departureBudget scale coefficient threshold +
        tailAmplitude * (parameters.unstableAmplitude / threshold) ^ (3 / 4 : ℝ) * scale ^ (3 / 4 : ℝ)) /
          (parameters.growth * coefficient) := by
    apply delayBound.trans
    apply div_le_div_of_nonneg_right _ (mul_pos parameters.growthPositive coefficientPositive).le
    exact mul_le_mul_of_nonneg_left (add_le_add_right budgetBound _) (by norm_num)
  have slowBound := mul_le_mul_of_nonneg_left
    (delay_slow_exponential_bound parameters.growthPositive scalePositive scaleBound cutoffPositive parameters.slowGrowth)
    parameters.stableNonnegative
  have fullStableBound : system.stable stopped ≤ parameters.fastStable * parameters.smallness * parameters.departureCutoff coefficient threshold +
      parameters.stableInitial * (parameters.departureCutoff coefficient threshold) ^ (parameters.slowRate / parameters.growth) * scale ^ (3 / 4 : ℝ) := by
    apply stableBound.trans
    have estimate := add_le_add_left slowBound
      (parameters.fastStable * parameters.smallness * parameters.departureCutoff coefficient threshold)
    convert estimate using 1 <;> dsimp only [MemorySaddleParameters.departureHorizon] <;> ring
  exact ⟨excluded, hit, afterEarly, fullDelayBound, fullStableBound⟩

end MemorySaddleSystem
end EulerNonuniqueness.Section6
