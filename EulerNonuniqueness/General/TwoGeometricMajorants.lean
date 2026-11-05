import Mathlib.Analysis.SpecificLimits.Normed

namespace EulerNonuniqueness.General

theorem summable_and_tsum_le_of_two_geometric_majorants
    (terms : ℕ → ℝ) (firstConstant secondConstant firstRatio secondRatio : ℝ)
    (termsNonnegative : ∀ index, 0 ≤ terms index)
    (firstNonnegative : 0 ≤ firstRatio) (firstSmall : firstRatio < 1)
    (secondNonnegative : 0 ≤ secondRatio) (secondSmall : secondRatio < 1)
    (bounded : ∀ index, terms index ≤ firstConstant * firstRatio ^ index + secondConstant * secondRatio ^ index) :
    Summable terms ∧ (∑' index, terms index) ≤
      firstConstant * (1 - firstRatio)⁻¹ + secondConstant * (1 - secondRatio)⁻¹ := by
  have firstSummable := (summable_geometric_of_lt_one firstNonnegative firstSmall).mul_left firstConstant
  have secondSummable := (summable_geometric_of_lt_one secondNonnegative secondSmall).mul_left secondConstant
  have actual := Summable.of_nonneg_of_le termsNonnegative bounded (firstSummable.add secondSummable)
  refine ⟨actual, ?_⟩
  have estimate := actual.tsum_le_tsum bounded (firstSummable.add secondSummable)
  simpa only [firstSummable.tsum_add secondSummable, tsum_mul_left,
    tsum_geometric_of_lt_one firstNonnegative firstSmall,
    tsum_geometric_of_lt_one secondNonnegative secondSmall] using estimate

end EulerNonuniqueness.General
