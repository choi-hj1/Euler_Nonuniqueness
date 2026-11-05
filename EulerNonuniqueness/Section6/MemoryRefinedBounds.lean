import EulerNonuniqueness.Section6.MemoryEnvelope

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem memory_refined_stable_bound {unstable stable history returned : ℝ → ℝ}
    {rate growth slowRate horizon multiplier smallness chart unstableBound stableBound historyBound initial : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (multiplierNonnegative : 0 ≤ multiplier)
    (smallnessNonnegative : 0 ≤ smallness) (chartNonnegative : 0 ≤ chart)
    (unstableBoundNonnegative : 0 ≤ unstableBound) (stableBoundNonnegative : 0 ≤ stableBound)
    (historyBoundNonnegative : 0 ≤ historyBound) (initialNonnegative : 0 ≤ initial)
    (fastRateBound : rate + multiplier * chart < growth)
    (slowRateBound : rate + multiplier * chart < slowRate)
    (unstableContinuous : ContinuousOn unstable (Icc 0 horizon))
    (stableContinuous : ContinuousOn stable (Icc 0 horizon))
    (historyContinuous : ContinuousOn history (Icc 0 horizon))
    (returnedContinuous : ContinuousOn returned (Icc 0 horizon))
    (unstableEnvelope : ∀ time ∈ Icc 0 horizon, unstable time ≤ unstableBound * Real.exp (growth * time))
    (historyEnvelope : ∀ time ∈ Icc 0 horizon, history time ≤ historyBound * Real.exp (growth * time))
    (returnedEnvelope : ∀ time ∈ Icc 0 horizon, returned time ≤
      smallness * (unstableBound + stableBound + historyBound) * Real.exp (growth * time))
    (inequality : ∀ time ∈ Icc 0 horizon, stable time ≤ initial * Real.exp (rate * time) +
      multiplier * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
        (smallness * unstable current + chart * stable current + smallness * history current + returned current)) :
    ∀ time ∈ Icc 0 horizon, stable time ≤
      multiplier * smallness * (2 * unstableBound + stableBound + 2 * historyBound) /
        (growth - (rate + multiplier * chart)) * Real.exp (growth * time) + initial * Real.exp (slowRate * time) := by
  let forcing := fun time => smallness * unstable time + smallness * history time + returned time
  have forcingContinuous : ContinuousOn forcing (Icc 0 horizon) :=
    ((continuousOn_const.mul unstableContinuous).add (continuousOn_const.mul historyContinuous)).add returnedContinuous
  have forcingBound : ∀ time ∈ Icc 0 horizon, forcing time ≤
      (smallness * (2 * unstableBound + stableBound + 2 * historyBound)) * Real.exp (growth * time) +
        0 * Real.exp (slowRate * time) := by
    intro time inside
    have estimate := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (unstableEnvelope time inside) smallnessNonnegative)
      (mul_le_mul_of_nonneg_left (historyEnvelope time inside) smallnessNonnegative)) (returnedEnvelope time inside)
    convert estimate using 1 <;> dsimp only [forcing] <;> ring
  have inequality' : ∀ time ∈ Icc 0 horizon, stable time ≤ initial * Real.exp (rate * time) +
      multiplier * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
        (forcing current + chart * stable current) := by
    intro time inside
    convert inequality time inside using 1
    congr 2
    apply intervalIntegral.integral_congr
    intro current _
    change Real.exp (rate * (time - current)) * (forcing current + chart * stable current) = _
    dsimp only [forcing]
    ring
  have bound := volterra_two_exponential_bound stableContinuous forcingContinuous initialNonnegative
    chartNonnegative multiplierNonnegative horizonNonnegative (by positivity) le_rfl
    fastRateBound slowRateBound forcingBound inequality'
  intro time inside
  convert bound time inside using 1 <;> ring

end EulerNonuniqueness.Section6
