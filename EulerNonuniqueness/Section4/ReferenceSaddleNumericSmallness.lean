import EulerNonuniqueness.Section4.ReferenceComputedSaddleBound
import EulerNonuniqueness.Section1.UniformInitialScaleSmallness

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_reference_saddle_numeric (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {internal memory bound momentRadius radius : ℝ}
    (internalNonnegative : 0 ≤ internal) (memoryNonnegative : 0 ≤ memory)
    (boundNonnegative : 0 ≤ bound) (momentRadiusPositive : 0 < momentRadius) (radiusPositive : 0 < radius) :
    ∀ᶠ frequency : ℝ in atTop, 1 ≤ frequency ∧ ∀ index : ℕ,
      ({scales with frequency := frequency}).length index < momentRadius / (8 * (memory + 1)) ∧
      referenceShapeForcingBudget {scales with frequency := frequency} index internal memory bound ≤
        ({scales with frequency := frequency}).omega index * radius / 16 := by
  let first := (2 * internal * memory ^ 2 + 27648) / Real.pi
  let second := (414720000000 + 3397386240 / Real.pi) * bound / scales.amplitude
  have firstNonnegative : 0 ≤ first := by dsimp only [first]; positivity
  have secondNonnegative : 0 ≤ second := by dsimp only [second]; positivity
  have tolerancePositive : 0 < momentRadius / (8 * (memory + 1)) := by positivity
  have lengthSmall := scales.eventually_length_lt_location ratioBound alphaPositive tolerancePositive
  have strainSmall := (scales.strain_tendsto_zero ratioBound alphaPositive).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (16 * (first + second) / radius),
    lengthSmall, strainSmall] with frequency frequencyBound frequencyLarge lengthSmall strainSmall
  refine ⟨frequencyBound, ?_⟩
  intro index
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have omegaBound : frequency ≤ changed.omega index := changed.omega_ge_frequency frequencyPositive (by linarith) index
  have omegaOne : 1 ≤ changed.omega index := frequencyBound.trans omegaBound
  have powerOne : 1 ≤ changed.omega index ^ 4 := one_le_pow₀ omegaOne
  constructor
  · exact (lengthSmall index).trans_le (mul_le_of_le_one_right tolerancePositive.le (scales.location_le_one index))
  · have budgetBound : referenceShapeForcingBudget changed index internal memory bound ≤ first + second := by
      change first * changed.strain + second / changed.omega index ^ 4 ≤ first + second
      exact add_le_add
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left strainSmall.le firstNonnegative)
        (div_le_self secondNonnegative powerOne)
    have frequencyCost : first + second ≤ frequency * radius / 16 := by
      have multiplied := (div_le_iff₀ radiusPositive).mp frequencyLarge
      linarith only [multiplied]
    exact budgetBound.trans (frequencyCost.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right omegaBound radiusPositive.le) (by norm_num)))

end EulerNonuniqueness.Paper
