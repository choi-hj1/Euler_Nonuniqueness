import Mathlib

noncomputable section

open Set
open scoped Topology ContDiff

namespace Complex

theorem exists_smooth_annular_cutoff (center : ℂ) {inner outer : ℝ}
    (innerPositive : 0 < inner) (ordered : inner < outer) :
    ∃ cutoff : ℂ → ℝ, ContDiff ℝ ∞ cutoff ∧ HasCompactSupport cutoff ∧
      (∀ position, 0 ≤ cutoff position ∧ cutoff position ≤ 1) ∧
      (∀ position, ‖position - center‖ ≤ inner / 2 → cutoff position = 0) ∧
      (∀ position, inner ≤ ‖position - center‖ → ‖position - center‖ ≤ outer → cutoff position = 1) ∧
      ∀ position, 2 * outer ≤ ‖position - center‖ → cutoff position = 0 := by
  have outerPositive : 0 < outer := innerPositive.trans ordered
  have innerDenominatorPositive : 0 < inner ^ 2 - (inner / 2) ^ 2 := by nlinarith
  have outerDenominatorPositive : 0 < (2 * outer) ^ 2 - outer ^ 2 := by nlinarith
  let cutoff : ℂ → ℝ := fun position =>
    Real.smoothTransition ((‖position - center‖ ^ 2 - (inner / 2) ^ 2) / (inner ^ 2 - (inner / 2) ^ 2)) *
      Real.smoothTransition (((2 * outer) ^ 2 - ‖position - center‖ ^ 2) / ((2 * outer) ^ 2 - outer ^ 2))
  have smooth : ContDiff ℝ ∞ cutoff := by
    have radial : ContDiff ℝ ∞ (fun position : ℂ => ‖position - center‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    exact (Real.smoothTransition.contDiff.comp ((radial.sub contDiff_const).div_const _)).mul
      (Real.smoothTransition.contDiff.comp ((contDiff_const.sub radial).div_const _))
  have outerZero (position : ℂ) (large : 2 * outer ≤ ‖position - center‖) : cutoff position = 0 := by
    have quotientNonpositive : ((2 * outer) ^ 2 - ‖position - center‖ ^ 2) /
        ((2 * outer) ^ 2 - outer ^ 2) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ outerDenominatorPositive.le
      nlinarith [norm_nonneg (position - center)]
    simp only [cutoff, Real.smoothTransition.zero_of_nonpos quotientNonpositive, mul_zero]
  have compact : HasCompactSupport cutoff := by
    apply HasCompactSupport.intro (isCompact_closedBall center (2 * outer))
    intro position outside
    exact outerZero position (le_of_lt (by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using outside))
  refine ⟨cutoff, smooth, compact, ?_, ?_, ?_, outerZero⟩
  · intro position
    exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
      mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)⟩
  · intro position small
    have quotientNonpositive : (‖position - center‖ ^ 2 - (inner / 2) ^ 2) /
        (inner ^ 2 - (inner / 2) ^ 2) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ innerDenominatorPositive.le
      nlinarith [norm_nonneg (position - center)]
    simp only [cutoff, Real.smoothTransition.zero_of_nonpos quotientNonpositive, zero_mul]
  · intro position lower upper
    have innerAtLeastOne : 1 ≤ (‖position - center‖ ^ 2 - (inner / 2) ^ 2) /
        (inner ^ 2 - (inner / 2) ^ 2) := by
      apply (one_le_div innerDenominatorPositive).mpr
      nlinarith [norm_nonneg (position - center)]
    have outerAtLeastOne : 1 ≤ ((2 * outer) ^ 2 - ‖position - center‖ ^ 2) /
        ((2 * outer) ^ 2 - outer ^ 2) := by
      apply (one_le_div outerDenominatorPositive).mpr
      nlinarith [norm_nonneg (position - center)]
    simp only [cutoff, Real.smoothTransition.one_of_one_le innerAtLeastOne,
      Real.smoothTransition.one_of_one_le outerAtLeastOne, mul_one]

end Complex
