import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_cascade_source_rate_ratio_threshold
    {alpha coefficient : ℝ} (alphaPositive : 0 < alpha) (alphaSmall : alpha < 1)
    (_coefficientNonnegative : 0 ≤ coefficient) (coefficientSmall : coefficient < 1 / 8)
    (requestedMin constant : ℝ) :
    ∃ threshold ≥ max (2 : ℝ) requestedMin, ∀ ratio : ℝ, threshold ≤ ratio →
      4 < ratio ^ alpha ∧
      constant ≤ ratio ^ alpha * (ratio ^ (1 - alpha) - 1) ∧
      8 * (coefficient * ratio + 1) ≤ ratio ^ alpha * (ratio ^ (1 - alpha) - 1) := by
  have gapPositive : 0 < 1 - 8 * coefficient := by linarith only [coefficientSmall]
  have powerDecay : Tendsto (fun ratio : ℝ => ratio ^ alpha / ratio) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (show 0 < 1 - alpha by linarith only [alphaSmall])).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ratio ratioPositive
    rw [show -(1 - alpha) = alpha - 1 by ring, Real.rpow_sub_one ratioPositive.ne']
  have reciprocalDecay : Tendsto (fun ratio : ℝ => 8 / ratio) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun ratio : ℝ => ratio⁻¹) atTop (𝓝 0)).const_mul 8
  have combinedDecay := powerDecay.add reciprocalDecay
  simp only [zero_add] at combinedDecay
  have eventual : ∀ᶠ ratio : ℝ in atTop,
      max (2 : ℝ) requestedMin ≤ ratio ∧
      4 < ratio ^ alpha ∧
      constant ≤ ratio ^ alpha * (ratio ^ (1 - alpha) - 1) ∧
      8 * (coefficient * ratio + 1) ≤ ratio ^ alpha * (ratio ^ (1 - alpha) - 1) := by
    filter_upwards [eventually_ge_atTop (max (2 : ℝ) requestedMin), eventually_ge_atTop (2 * constant),
      (tendsto_rpow_atTop alphaPositive).eventually (eventually_gt_atTop (4 : ℝ)),
      powerDecay.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      combinedDecay.eventually (eventually_lt_nhds gapPositive)]
      with ratio ratioLarge constantLarge powerLarge powerSmall combinedSmall
    have ratioPositive : 0 < ratio := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      ((le_max_left _ _).trans ratioLarge)
    have identity : ratio ^ alpha * (ratio ^ (1 - alpha) - 1) = ratio - ratio ^ alpha := by
      rw [mul_sub, ← Real.rpow_add ratioPositive, show alpha + (1 - alpha) = 1 by ring, Real.rpow_one, mul_one]
    have powerBound := (div_lt_iff₀ ratioPositive).mp powerSmall
    have constantBound : constant ≤ ratio - ratio ^ alpha := by nlinarith only [powerBound, constantLarge]
    have normalized : (ratio ^ alpha + 8) / ratio < 1 - 8 * coefficient := by
      simpa only [add_div] using combinedSmall
    have receiverBound : 8 * (coefficient * ratio + 1) ≤ ratio - ratio ^ alpha := by
      have scaled := (div_lt_iff₀ ratioPositive).mp normalized
      nlinarith only [scaled]
    exact ⟨ratioLarge, powerLarge, by rwa [identity], by rwa [identity]⟩
  obtain ⟨threshold, large⟩ := eventually_atTop.1 eventual
  exact ⟨threshold, (large threshold le_rfl).1, fun ratio bound => (large ratio bound).2⟩

end EulerNonuniqueness.Paper
