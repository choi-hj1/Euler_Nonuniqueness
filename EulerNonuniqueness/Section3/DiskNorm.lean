import EulerNonuniqueness.Section3.DiskLp

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem diskDensity_eLpNorm_toReal (center : Plane) (radius amplitude : ℝ)
    (radiusNonnegative : 0 ≤ radius) {exponent : ℝ} (exponentPositive : 0 < exponent) :
    (eLpNorm (diskDensity center radius amplitude) (ENNReal.ofReal exponent) volume).toReal =
      |amplitude| * (Real.pi * radius ^ 2) ^ (1 / exponent) := by
  rw [diskDensity, eLpNorm_indicator_const measurableSet_ball
    (ENNReal.ofReal_pos.mpr exponentPositive).ne' ENNReal.ofReal_ne_top,
    volume_complex_ball_of_nonneg center radiusNonnegative,
    ← ofReal_norm_eq_enorm, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (norm_nonneg amplitude),
    ENNReal.toReal_ofReal (show 0 ≤ Real.pi * radius ^ 2 by positivity),
    ENNReal.toReal_ofReal exponentPositive.le, Real.norm_eq_abs]

theorem diskDensity_integral (center : Plane) (radius amplitude : ℝ)
    (radiusNonnegative : 0 ≤ radius) :
    (∫ position, diskDensity center radius amplitude position) =
      Real.pi * radius ^ 2 * amplitude := by
  rw [diskDensity, integral_indicator_const _ measurableSet_ball]
  change (volume (Metric.ball center radius)).toReal * amplitude = _
  rw [volume_complex_ball_of_nonneg center radiusNonnegative,
    ENNReal.toReal_ofReal (show 0 ≤ Real.pi * radius ^ 2 by positivity)]

theorem diskDensity_support_subset (center : Plane) (radius amplitude : ℝ) :
    Function.support (diskDensity center radius amplitude) ⊆ Metric.ball center radius :=
  support_indicator_subset

end EulerNonuniqueness.Paper
