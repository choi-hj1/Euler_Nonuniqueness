import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

namespace EulerNonuniqueness.General

theorem summable_weighted_norm_of_eq_add_finite_corrections {Index Space : Type*}
    [NormedAddCommGroup Space] (selected : Finset Index) (weight : ℕ → ℝ)
    (nonnegative : ∀ power, 0 ≤ weight power) (actual principal : ℕ → Space)
    (correction : Index → ℕ → Space)
    (identity : ∀ power, actual power = principal power + ∑ index ∈ selected, correction index power)
    (principalSummable : Summable (fun power => weight power * ‖principal power‖))
    (correctionSummable : ∀ index ∈ selected, Summable (fun power => weight power * ‖correction index power‖)) :
    Summable (fun power => weight power * ‖actual power‖) ∧
      (∑' power, weight power * ‖actual power‖) ≤
        (∑' power, weight power * ‖principal power‖) +
          ∑ index ∈ selected, ∑' power, weight power * ‖correction index power‖ := by
  have bound (power : ℕ) : weight power * ‖actual power‖ ≤
      weight power * ‖principal power‖ + ∑ index ∈ selected, weight power * ‖correction index power‖ := by
    rw [identity power, ← Finset.mul_sum, ← mul_add]
    exact mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add_left (norm_sum_le _ _) _)) (nonnegative power)
  have majorant := principalSummable.add (summable_sum correctionSummable)
  have actualSummable := Summable.of_nonneg_of_le (fun power => mul_nonneg (nonnegative power) (norm_nonneg _)) bound majorant
  refine ⟨actualSummable, ?_⟩
  have estimate := actualSummable.tsum_le_tsum bound majorant
  rw [principalSummable.tsum_add (summable_sum correctionSummable), Summable.tsum_finsetSum correctionSummable] at estimate
  exact estimate

end EulerNonuniqueness.General
