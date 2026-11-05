import EulerNonuniqueness.Section6.MemorySaddleConstants
import EulerNonuniqueness.Section6.DelayPowerBounds

noncomputable section

namespace EulerNonuniqueness.Section6.MemorySaddleParameters

theorem remainderBudget_mono (parameters : MemorySaddleParameters) {scale cutoff first second : ℝ}
    (scaleNonnegative : 0 ≤ scale) (ordered : first ≤ second) :
    parameters.remainderBudget scale cutoff first ≤ parameters.remainderBudget scale cutoff second := by
  have multiplierNonnegative := parameters.constants_nonnegative.2.2.2
  have smallnessNonnegative := parameters.smallnessNonnegative
  have stableNonnegative := parameters.stableNonnegative
  have driveNonnegative := parameters.driveNonnegative
  have slowPositive := parameters.slowPositive
  have firstBound := mul_le_mul_of_nonneg_left ordered (mul_nonneg multiplierNonnegative smallnessNonnegative)
  have exponentialBound := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ordered slowPositive.le)
  have lastBound := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left exponentialBound
    (by positivity : 0 ≤ parameters.remainderMultiplier * (parameters.stableInitial + parameters.driveAmplitude) * scale)) slowPositive.le
  exact add_le_add (add_le_add_right firstBound _) lastBound

theorem remainderBudget_at_delay_le (parameters : MemorySaddleParameters) {scale cutoff : ℝ}
    (scalePositive : 0 < scale) (scaleBound : scale ≤ 1) (cutoffPositive : 0 < cutoff) :
    parameters.remainderBudget scale cutoff (Real.log (cutoff / scale) / parameters.growth) ≤
      parameters.remainderMultiplier * parameters.smallness * (Real.log (cutoff / scale) / parameters.growth) +
        parameters.remainderMultiplier * parameters.fastStable * parameters.smallness * cutoff / parameters.growth +
        (parameters.remainderMultiplier * (parameters.stableInitial + parameters.driveAmplitude) / parameters.slowRate) *
          cutoff ^ (parameters.slowRate / parameters.growth) * scale ^ (3 / 4 : ℝ) := by
  have multiplierNonnegative := parameters.constants_nonnegative.2.2.2
  have stableNonnegative := parameters.stableNonnegative
  have driveNonnegative := parameters.driveNonnegative
  have slowPositive := parameters.slowPositive
  have bounded := mul_le_mul_of_nonneg_left
    (delay_slow_exponential_bound parameters.growthPositive scalePositive scaleBound cutoffPositive parameters.slowGrowth)
    (by positivity : 0 ≤ parameters.remainderMultiplier * (parameters.stableInitial + parameters.driveAmplitude) / parameters.slowRate)
  have estimate := add_le_add_left bounded
    (parameters.remainderMultiplier * parameters.smallness * (Real.log (cutoff / scale) / parameters.growth) +
      parameters.remainderMultiplier * parameters.fastStable * parameters.smallness * cutoff / parameters.growth)
  convert estimate using 1 <;> dsimp only [remainderBudget] <;> ring

end EulerNonuniqueness.Section6.MemorySaddleParameters
