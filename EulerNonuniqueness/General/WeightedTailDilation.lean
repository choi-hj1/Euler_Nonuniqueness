import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

namespace EulerNonuniqueness.General

theorem summable_weighted_tail_dilation {Space : Type*} [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] (values : ℕ → Space) {weight ratio : ℝ}
    (weightNonnegative : 0 ≤ weight) (ratioNonnegative : 0 ≤ ratio) (ratioSmall : ratio ≤ 1)
    (summable : Summable (fun power => weight ^ (power + 1) * ‖values power‖)) :
    Summable (fun power => weight ^ (power + 1) *
      ‖if power = 0 then 0 else ratio ^ power • values power‖) ∧
      (∑' power, weight ^ (power + 1) *
        ‖if power = 0 then 0 else ratio ^ power • values power‖) ≤
          ratio * (∑' power, weight ^ (power + 1) * ‖values power‖) := by
  have pointwise (power : ℕ) : weight ^ (power + 1) *
      ‖if power = 0 then 0 else ratio ^ power • values power‖ ≤
        ratio * (weight ^ (power + 1) * ‖values power‖) := by
    by_cases zero : power = 0
    · subst power
      simpa only [ite_true, norm_zero, mul_zero] using
        (mul_nonneg ratioNonnegative
          (mul_nonneg (pow_nonneg weightNonnegative (0 + 1)) (norm_nonneg (values 0))))
    · rw [if_neg zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg ratioNonnegative power)]
      have powerBound := pow_le_of_le_one ratioNonnegative ratioSmall zero
      calc
        weight ^ (power + 1) * (ratio ^ power * ‖values power‖) ≤
            weight ^ (power + 1) * (ratio * ‖values power‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right powerBound (norm_nonneg _))
            (pow_nonneg weightNonnegative _)
        _ = ratio * (weight ^ (power + 1) * ‖values power‖) := by ac_rfl
  have actual := Summable.of_nonneg_of_le (fun power => by positivity)
    pointwise (summable.mul_left ratio)
  refine ⟨actual, ?_⟩
  exact (actual.tsum_le_tsum pointwise (summable.mul_left ratio)).trans_eq (tsum_mul_left ..)

end EulerNonuniqueness.General
