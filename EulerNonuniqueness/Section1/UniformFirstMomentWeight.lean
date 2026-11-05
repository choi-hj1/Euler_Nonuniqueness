import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_uniform_firstMoment_saddle_weight (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      0 < 2 * Real.sqrt 2 * changed.omega index ∧
      2 * (96 / Real.pi * (2304 * changed.strain)) ≤ 2 * Real.sqrt 2 * changed.omega index := by
  let coefficient := 96 / Real.pi * 2304
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have sqrtOne : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  filter_upwards [eventually_ge_atTop (max 1 coefficient),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyLarge strainSmall
  intro index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaFrequency := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) index
  have omegaPositive : 0 < changed.omega index := (zero_lt_one.trans_le frequencyOne).trans_le omegaFrequency
  have omegaCoefficient : coefficient ≤ changed.omega index :=
    ((le_max_right _ _).trans frequencyLarge).trans omegaFrequency
  have strainCoefficient : 96 / Real.pi * (2304 * changed.strain) ≤ coefficient := by
    have actual := mul_le_mul_of_nonneg_left strainSmall.le coefficientNonnegative
    simpa only [coefficient, mul_assoc, mul_one] using actual
  refine ⟨by positivity, ?_⟩
  have frequencyGrowth := mul_le_mul_of_nonneg_right sqrtOne omegaPositive.le
  nlinarith

end EulerNonuniqueness.Paper
