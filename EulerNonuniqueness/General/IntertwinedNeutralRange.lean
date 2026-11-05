import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem inverse_intertwined_range_neutral_zero
    (neutral generator originalGenerator : Space →L[ℝ] Space) (coordinates : Space ≃L[ℝ] Space)
    (annihilates : ∀ direction, neutral (generator direction) = 0)
    (intertwines : ∀ direction, originalGenerator (coordinates direction) = coordinates (generator direction))
    (preimage : Space) : neutral (coordinates.symm (originalGenerator preimage)) = 0 := by
  have actual := intertwines (coordinates.symm preimage)
  rw [coordinates.apply_symm_apply] at actual
  rw [actual, coordinates.symm_apply_apply]
  exact annihilates _

end EulerNonuniqueness.General
