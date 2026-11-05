import EulerNonuniqueness.Section5.CascadeProof
import EulerNonuniqueness.Section1.PolynomialSeedSmallness

noncomputable section

open Filter
open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.predictedTime_index_le_total (scales : Scales) (sectionTime : ℝ)
    {count index : ℕ} (indexOne : 1 ≤ index)
    (nonnegative : ∀ next : ℕ, 1 ≤ next → 0 ≤ scales.delay sectionTime next)
    (summable : Summable (fun next : ℕ => scales.delay sectionTime (next + 1))) :
    scales.predictedTime sectionTime count index ≤
      ∑' next : ℕ, scales.delay sectionTime (next + 1) := by
  have smaller : scales.predictedTime sectionTime count index ≤
      scales.predictedTime sectionTime count 1 := by
    unfold Scales.predictedTime
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro next member
      have bounds := Finset.mem_Ico.mp member
      exact Finset.mem_Ico.mpr ⟨indexOne.trans bounds.1, bounds.2⟩
    · intro next member _
      exact nonnegative next (Finset.mem_Ico.mp member).1
  exact smaller.trans (scales.predictedTime_one_le_total sectionTime count nonnegative summable)

/-- The predicted times are uniformly below one quarter, independently of count and index. -/
theorem Scales.eventually_predictedTime_index_lt_quarter (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (alphaSmall : scales.alpha < 1) {sectionTime : ℝ} (sectionPositive : 0 < sectionTime) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count index : ℕ, 1 ≤ index →
      ({scales with frequency := frequency} : Scales).predictedTime sectionTime count index < 1 / 4 := by
  have ratioOne : 1 < scales.ratio := by linarith only [ratioBound]
  filter_upwards [scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive 0
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_actual_delay_total_lt ratioOne alphaSmall sectionTime (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_gt_atTop (0 : ℝ)] with frequency tiny total frequencyPositive
  let changed : Scales := {scales with frequency := frequency}
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have seedSmall (index : ℕ) : changed.seed index < 1 := by
    simpa only [pow_zero, Real.rpow_one, one_mul] using tiny index
  have nonnegative (next : ℕ) (_nextOne : 1 ≤ next) : 0 ≤ changed.delay sectionTime next :=
    (changed.actual_delay_pos frequencyPositive ratioPositive sectionPositive next (seedSmall next)).le
  have summable := changed.actual_delay_summable frequencyPositive ratioOne alphaSmall sectionTime
  intro count index indexOne
  exact (changed.predictedTime_index_le_total sectionTime indexOne nonnegative summable).trans_lt total

end EulerNonuniqueness.Paper
