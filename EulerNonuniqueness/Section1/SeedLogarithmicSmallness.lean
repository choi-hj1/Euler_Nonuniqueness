import EulerNonuniqueness.Section1.PolynomialSeedSmallness

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_seed_logarithmic_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {precision : ℝ} (precisionPositive : 0 < precision) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      0 < changed.seed index ∧ changed.seed index ≤ 1 ∧
        changed.seed index * Real.log ((changed.seed index)⁻¹) < precision := by
  filter_upwards [scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive 0
      (by norm_num : (0 : ℝ) < 1 / 2) (by positivity : 0 < precision / 2),
    scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive 0
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with frequency rootSmall seedSmall frequencyPositive
  intro index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have seedPositive : 0 < changed.seed index := changed.seed_pos frequencyPositive ratioPositive index
  have rootBound : changed.seed index ^ (1 / 2 : ℝ) < precision / 2 := by
    simpa only [pow_zero, one_mul] using rootSmall index
  have seedBound : changed.seed index < 1 := by
    simpa only [pow_zero, one_mul, Real.rpow_one] using seedSmall index
  have logarithm := Real.log_le_rpow_div (inv_nonneg.mpr seedPositive.le)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have powerIdentity : changed.seed index * (changed.seed index)⁻¹ ^ (1 / 2 : ℝ) =
      changed.seed index ^ (1 / 2 : ℝ) := by
    rw [Real.inv_rpow seedPositive.le, ← Real.rpow_neg seedPositive.le]
    calc
      _ = changed.seed index ^ (1 : ℝ) * changed.seed index ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = changed.seed index ^ ((1 : ℝ) - 1 / 2) := by rw [sub_eq_add_neg, Real.rpow_add seedPositive]
      _ = _ := by norm_num
  have bound := mul_le_mul_of_nonneg_left logarithm seedPositive.le
  have majorized : changed.seed index * Real.log ((changed.seed index)⁻¹) ≤
      2 * changed.seed index ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ changed.seed index * ((changed.seed index)⁻¹ ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) := bound
      _ = _ := by rw [div_eq_mul_inv]; norm_num; nlinarith only [powerIdentity]
  exact ⟨seedPositive, seedBound.le, majorized.trans_lt (by linarith only [rootBound])⟩

end EulerNonuniqueness.Paper
