import EulerNonuniqueness.Section6.MemorySmallness

noncomputable section

namespace EulerNonuniqueness.Section6

structure MemorySaddleParameters where
  growth : ℝ
  slowRate : ℝ
  rate : ℝ
  multiplier : ℝ
  gain : ℝ
  smallness : ℝ
  chart : ℝ
  unstableAmplitude : ℝ
  directAmplitude : ℝ
  stableInitial : ℝ
  historyInitial : ℝ
  driveAmplitude : ℝ
  growthPositive : 0 < growth
  slowPositive : 0 < slowRate
  multiplierNonnegative : 0 ≤ multiplier
  gainNonnegative : 0 ≤ gain
  smallnessNonnegative : 0 ≤ smallness
  chartNonnegative : 0 ≤ chart
  unstableNonnegative : 0 ≤ unstableAmplitude
  directNonnegative : 0 ≤ directAmplitude
  stableNonnegative : 0 ≤ stableInitial
  historyNonnegative : 0 ≤ historyInitial
  driveNonnegative : 0 ≤ driveAmplitude
  slowGrowth : slowRate ≤ growth / 4
  slowRateBound : rate + multiplier * chart < slowRate
  gainBound : multiplier / (growth - rate) ≤ gain
  smallnessBound : smallness ≤ 1
  chartSmall : gain * chart ≤ 1 / 8
  linearSmall : gain * smallness ≤ 1 / 64
  quadraticSmall : gain ^ 2 * smallness ≤ 1 / 64

namespace MemorySaddleParameters

def determinant (parameters : MemorySaddleParameters) : ℝ :=
  (1 - parameters.gain * (parameters.chart + parameters.smallness)) *
    (1 - 2 * parameters.gain * parameters.smallness) -
      (2 * parameters.gain * parameters.smallness) * (parameters.gain * (1 + parameters.smallness))

def coarseStable (parameters : MemorySaddleParameters) : ℝ :=
  ((1 - 2 * parameters.gain * parameters.smallness) *
      (parameters.stableInitial + 2 * parameters.gain * parameters.smallness * parameters.unstableAmplitude) +
    (2 * parameters.gain * parameters.smallness) *
      (parameters.historyInitial + parameters.gain * ((1 + parameters.smallness) * parameters.unstableAmplitude + parameters.driveAmplitude))) /
        parameters.determinant

def coarseHistory (parameters : MemorySaddleParameters) : ℝ :=
  ((1 - parameters.gain * (parameters.chart + parameters.smallness)) *
      (parameters.historyInitial + parameters.gain * ((1 + parameters.smallness) * parameters.unstableAmplitude + parameters.driveAmplitude)) +
    (parameters.gain * (1 + parameters.smallness)) *
      (parameters.stableInitial + 2 * parameters.gain * parameters.smallness * parameters.unstableAmplitude)) /
        parameters.determinant

def fastStable (parameters : MemorySaddleParameters) : ℝ :=
  parameters.multiplier * (2 * parameters.unstableAmplitude + parameters.coarseStable + 2 * parameters.coarseHistory) /
    (parameters.growth - (parameters.rate + parameters.multiplier * parameters.chart))

def remainderMultiplier (parameters : MemorySaddleParameters) : ℝ :=
  parameters.multiplier * (parameters.unstableAmplitude + parameters.coarseStable) +
    parameters.multiplier * parameters.coarseHistory +
    (parameters.unstableAmplitude + parameters.coarseStable + parameters.coarseHistory) +
    parameters.multiplier * (parameters.unstableAmplitude + parameters.coarseStable)

def remainderBudget (parameters : MemorySaddleParameters) (scale cutoff horizon : ℝ) : ℝ :=
  parameters.remainderMultiplier * parameters.smallness * horizon +
    parameters.remainderMultiplier * parameters.fastStable * parameters.smallness * cutoff / parameters.growth +
    parameters.remainderMultiplier * (parameters.stableInitial + parameters.driveAmplitude) * scale *
      Real.exp (parameters.slowRate * horizon) / parameters.slowRate

theorem diagonal_bounds (parameters : MemorySaddleParameters) :
    (3 / 4 : ℝ) ≤ 1 - parameters.gain * (parameters.chart + parameters.smallness) ∧
      (3 / 4 : ℝ) ≤ 1 - 2 * parameters.gain * parameters.smallness ∧
      (1 / 2 : ℝ) ≤ parameters.determinant :=
  memory_determinant_lower_bound parameters.gainNonnegative parameters.chartNonnegative
    parameters.smallnessNonnegative parameters.smallnessBound parameters.chartSmall parameters.linearSmall parameters.quadraticSmall

theorem determinant_positive (parameters : MemorySaddleParameters) : 0 < parameters.determinant :=
  lt_of_lt_of_le (by norm_num) parameters.diagonal_bounds.2.2

theorem effective_lt_growth (parameters : MemorySaddleParameters) :
    parameters.rate + parameters.multiplier * parameters.chart < parameters.growth := by
  nlinarith [parameters.slowRateBound, parameters.slowGrowth, parameters.growthPositive]

theorem rate_lt_growth (parameters : MemorySaddleParameters) : parameters.rate < parameters.growth := by
  have product := mul_nonneg parameters.multiplierNonnegative parameters.chartNonnegative
  linarith [parameters.effective_lt_growth]

theorem constants_nonnegative (parameters : MemorySaddleParameters) :
    0 ≤ parameters.coarseStable ∧ 0 ≤ parameters.coarseHistory ∧
      0 ≤ parameters.fastStable ∧ 0 ≤ parameters.remainderMultiplier := by
  have firstDiagonal : 0 ≤ 1 - parameters.gain * (parameters.chart + parameters.smallness) :=
    (by norm_num : (0 : ℝ) ≤ 3 / 4).trans parameters.diagonal_bounds.1
  have secondDiagonal : 0 ≤ 1 - 2 * parameters.gain * parameters.smallness :=
    (by norm_num : (0 : ℝ) ≤ 3 / 4).trans parameters.diagonal_bounds.2.1
  have determinantNonnegative := parameters.determinant_positive.le
  have gainNonnegative := parameters.gainNonnegative
  have smallnessNonnegative := parameters.smallnessNonnegative
  have unstableNonnegative := parameters.unstableNonnegative
  have stableNonnegative := parameters.stableNonnegative
  have historyNonnegative := parameters.historyNonnegative
  have driveNonnegative := parameters.driveNonnegative
  have multiplierNonnegative := parameters.multiplierNonnegative
  have stable : 0 ≤ parameters.coarseStable := by unfold coarseStable; positivity
  have history : 0 ≤ parameters.coarseHistory := by unfold coarseHistory; positivity
  have fast : 0 ≤ parameters.fastStable := by
    unfold fastStable
    have denominator := sub_pos.mpr parameters.effective_lt_growth
    positivity
  refine ⟨stable, history, fast, ?_⟩
  unfold remainderMultiplier
  positivity

theorem remainderBudget_nonnegative (parameters : MemorySaddleParameters) {scale cutoff horizon : ℝ}
    (scaleNonnegative : 0 ≤ scale) (cutoffNonnegative : 0 ≤ cutoff) (horizonNonnegative : 0 ≤ horizon) :
    0 ≤ parameters.remainderBudget scale cutoff horizon := by
  have multiplier := parameters.constants_nonnegative.2.2.2
  have fast := parameters.constants_nonnegative.2.2.1
  have smallness := parameters.smallnessNonnegative
  have stable := parameters.stableNonnegative
  have drive := parameters.driveNonnegative
  have growth := parameters.growthPositive
  have slow := parameters.slowPositive
  unfold remainderBudget
  positivity

end MemorySaddleParameters
end EulerNonuniqueness.Section6
