import EulerNonuniqueness.Section1.ForeignInteractionWeight
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_uniform_reference_tube_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {constant radius : ℝ} (constantNonnegative : 0 ≤ constant) (radiusPositive : 0 < radius) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      constant * (({scales with frequency := frequency}).strain / ({scales with frequency := frequency}).omega index +
        (({scales with frequency := frequency}).omega index)⁻¹ ^ 5) < radius := by
  have strainSmall := (scales.strain_tendsto_zero ratioBound alphaPositive).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_gt_atTop (2 * (constant + 1) / radius), strainSmall]
    with frequency frequencyBound frequencyLarge strainSmall
  intro index
  let actual : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyBound
  have omegaGe : frequency ≤ actual.omega index := actual.omega_ge_frequency frequencyPositive (by dsimp only [actual]; linarith) index
  have omegaOne : 1 ≤ actual.omega index := frequencyBound.trans omegaGe
  have omegaPositive : 0 < actual.omega index := zero_lt_one.trans_le omegaOne
  have powerFour : 1 ≤ actual.omega index ^ 4 := one_le_pow₀ omegaOne
  have powerFive : actual.omega index ≤ actual.omega index ^ 5 := by
    have multiplied := mul_le_mul_of_nonneg_left powerFour omegaPositive.le
    convert multiplied using 1 <;> ring
  have inversePower : (actual.omega index)⁻¹ ^ 5 ≤ (actual.omega index)⁻¹ := by
    rw [inv_pow]
    exact (inv_le_inv₀ (pow_pos omegaPositive 5) omegaPositive).mpr powerFive
  have scalarSmall : 2 * constant / frequency < radius := by
    apply (div_lt_iff₀ frequencyPositive).mpr
    have large := (div_lt_iff₀ radiusPositive).mp frequencyLarge
    nlinarith
  calc
    _ ≤ constant * (1 / actual.omega index + (actual.omega index)⁻¹) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (div_le_div_of_nonneg_right strainSmall.le omegaPositive.le) inversePower) constantNonnegative
    _ = 2 * constant / actual.omega index := by ring
    _ ≤ 2 * constant / frequency := div_le_div_of_nonneg_left (by positivity) frequencyPositive omegaGe
    _ < radius := scalarSmall

end EulerNonuniqueness.Paper
