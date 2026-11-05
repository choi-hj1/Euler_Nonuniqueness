import EulerNonuniqueness.General.ExponentialExposureInterpolation
import EulerNonuniqueness.Section1.PolynomialSeedSmallness

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_slow_seed_profile_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {theta tolerance : ℝ} (thetaNonnegative : 0 ≤ theta) (thetaLtOne : theta < 1)
    (power : ℕ) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, ∀ fast slow origin finish : ℝ,
      let changed : Scales := {scales with frequency := frequency}
      0 ≤ slow → slow ≤ theta * fast → origin ≤ finish →
      changed.seed index * Real.exp (fast * (finish - origin)) ≤ 1 →
      changed.omega index ^ power * changed.seed index *
        Real.exp (slow * (finish - origin)) < tolerance := by
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  filter_upwards [scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive power
      (sub_pos.mpr thetaLtOne) tolerancePositive, eventually_gt_atTop (0 : ℝ)] with
    frequency small frequencyPositive index fast slow origin finish
  dsimp only
  intro _slowNonnegative slowBound ordered exposure
  let changed : Scales := {scales with frequency := frequency}
  have interpolated := EulerNonuniqueness.General.exponential_exposure_interpolation
    (changed.seed_pos frequencyPositive ratioPositive index) zero_lt_one
    thetaNonnegative thetaLtOne.le ordered slowBound exposure
  rw [Real.one_rpow] at interpolated
  have polynomialNonnegative : 0 ≤ changed.omega index ^ power :=
    pow_nonneg (changed.omega_pos frequencyPositive ratioPositive index).le power
  have comparison := mul_le_mul_of_nonneg_left interpolated polynomialNonnegative
  have bound : changed.omega index ^ power * changed.seed index *
      Real.exp (slow * (finish - origin)) ≤ changed.omega index ^ power * changed.seed index ^ (1 - theta) := by
    simpa only [mul_assoc, mul_one] using comparison
  exact bound.trans_lt (small index)

end EulerNonuniqueness.Paper
