import EulerNonuniqueness.General.ExponentialHitElapsed
import EulerNonuniqueness.Section1.PolynomialSeedSmallness

noncomputable section

open Filter

namespace EulerNonuniqueness.Paper

/-- Uniform seed smallness forces a fixed positive profile hit after any fixed normalized time. -/
theorem Scales.eventually_fixed_level_hit_elapsed_gt (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {level magnitude : ℝ} (levelPositive : 0 < level)
    (magnitudeNonnegative : 0 ≤ magnitude) (bound : ℝ) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, ∀ exponent : ℝ,
      level ≤ magnitude * ({scales with frequency := frequency} : Scales).seed index * Real.exp exponent →
      bound < exponent := by
  have targetPositive : 0 < level * Real.exp (-bound) / (magnitude + 1) := by positivity
  filter_upwards [scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive 0
    (by norm_num : (0 : ℝ) < 1) targetPositive, eventually_gt_atTop (0 : ℝ)]
    with frequency seedSmall frequencyPositive
  intro index exponent profile
  apply EulerNonuniqueness.General.exponent_gt_of_fixed_level_exponential_profile
    (({scales with frequency := frequency} : Scales).seed_pos frequencyPositive
      (by change 0 < scales.ratio; linarith only [ratioBound]) index)
    magnitudeNonnegative profile
  simpa only [pow_zero, Real.rpow_one, one_mul] using seedSmall index

end EulerNonuniqueness.Paper
