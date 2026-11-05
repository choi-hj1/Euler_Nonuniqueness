import Mathlib

noncomputable section

open Set

namespace EulerNonuniqueness.General

variable {Domain Range : Type*} [PseudoMetricSpace Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem lipschitzWith_smul_of_supported_lipschitzOn
    (field : Domain → Range) (cutoff : Domain → ℝ) (admissible : Set Domain)
    (fieldConstant cutoffConstant bound : NNReal)
    (fieldLipschitz : LipschitzOnWith fieldConstant field admissible)
    (cutoffLipschitz : LipschitzWith cutoffConstant cutoff)
    (cutoffBound : ∀ point, |cutoff point| ≤ 1)
    (supported : ∀ point ∉ admissible, cutoff point = 0)
    (fieldBound : ∀ point ∈ admissible, ‖field point‖ ≤ bound) :
    LipschitzWith (fieldConstant + cutoffConstant * bound) (fun point => cutoff point • field point) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm]
  change ‖cutoff first • field first - cutoff second • field second‖ ≤
    ((fieldConstant + cutoffConstant * bound : NNReal) : ℝ) * dist first second
  simp only [NNReal.coe_add, NNReal.coe_mul]
  by_cases firstInside : first ∈ admissible
  · by_cases secondInside : second ∈ admissible
    · have split : cutoff first • field first - cutoff second • field second =
          cutoff first • (field first - field second) + (cutoff first - cutoff second) • field second := by
        module
      rw [split]
      have firstTerm : ‖cutoff first • (field first - field second)‖ ≤
          (fieldConstant : ℝ) * dist first second := by
        rw [norm_smul, Real.norm_eq_abs]
        calc
          _ ≤ 1 * ‖field first - field second‖ := mul_le_mul_of_nonneg_right (cutoffBound first) (norm_nonneg _)
          _ ≤ (fieldConstant : ℝ) * dist first second := by
            simpa only [one_mul, dist_eq_norm] using fieldLipschitz.dist_le_mul first firstInside second secondInside
      have secondTerm : ‖(cutoff first - cutoff second) • field second‖ ≤
          ((cutoffConstant : ℝ) * (bound : ℝ)) * dist first second := by
        rw [norm_smul, Real.norm_eq_abs]
        have difference : |cutoff first - cutoff second| ≤ (cutoffConstant : ℝ) * dist first second :=
          cutoffLipschitz.dist_le_mul first second
        calc
          _ ≤ ((cutoffConstant : ℝ) * dist first second) * (bound : ℝ) :=
            mul_le_mul difference (fieldBound second secondInside) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      exact (norm_add_le _ _).trans ((add_le_add firstTerm secondTerm).trans_eq (by ring))
    · rw [supported second secondInside, zero_smul, sub_zero, norm_smul, Real.norm_eq_abs]
      have difference : |cutoff first| ≤ (cutoffConstant : ℝ) * dist first second := by
        simpa only [supported second secondInside, sub_zero, Real.dist_eq] using cutoffLipschitz.dist_le_mul first second
      calc
        _ ≤ ((cutoffConstant : ℝ) * dist first second) * (bound : ℝ) :=
          mul_le_mul difference (fieldBound first firstInside) (norm_nonneg _) (by positivity)
        _ ≤ _ := by nlinarith [dist_nonneg (x := first) (y := second), fieldConstant.coe_nonneg]
  · by_cases secondInside : second ∈ admissible
    · rw [supported first firstInside, zero_smul, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs]
      have difference : |cutoff second| ≤ (cutoffConstant : ℝ) * dist first second := by
        simpa only [supported first firstInside, zero_sub, abs_neg, Real.dist_eq] using cutoffLipschitz.dist_le_mul first second
      calc
        _ ≤ ((cutoffConstant : ℝ) * dist first second) * (bound : ℝ) :=
          mul_le_mul difference (fieldBound second secondInside) (norm_nonneg _) (by positivity)
        _ ≤ _ := by nlinarith [dist_nonneg (x := first) (y := second), fieldConstant.coe_nonneg]
    · simp only [supported first firstInside, supported second secondInside, zero_smul, sub_self, norm_zero]
      positivity

end EulerNonuniqueness.General
