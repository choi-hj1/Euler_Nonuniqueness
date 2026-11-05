import Mathlib

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_sub_le_of_scalar_decompositions
    (initial final first second radial : Space) (initialMean finalMean : ℝ)
    (initialIdentity : initial = first + initialMean • radial)
    (finalIdentity : final = second + finalMean • radial) :
    ‖initial - final‖ ≤ ‖first - second‖ + ‖radial‖ * |initialMean - finalMean| := by
  have identity : initial - final = (first - second) + (initialMean - finalMean) • radial := by
    rw [initialIdentity, finalIdentity, sub_smul]
    abel
  rw [identity]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_eq_abs]; ring)

end EulerNonuniqueness.General
