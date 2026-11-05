import EulerNonuniqueness.General.CommonCoordinateWeightedInverse

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem weightedProjectionShapeBudget_le_of_weighted_inverse
    (transverse neutral : Space →L[ℝ] Space) (first final correctedFirst correctedFinal : Space)
    {weight inverseFactor : ℝ} (weightPositive : 0 < weight) (inverseNonnegative : 0 ≤ inverseFactor)
    (inverse : weightedProjectionDistance transverse neutral weight first final ≤
      inverseFactor * weightedProjectionDistance transverse neutral weight correctedFirst correctedFinal) :
    ‖transverse first - transverse final‖ +
        (‖transverse first‖ + ‖transverse final‖) * ‖neutral first - neutral final‖ ≤
      inverseFactor * max 1 ((‖transverse first‖ + ‖transverse final‖) / weight) *
        weightedProjectionDistance transverse neutral weight correctedFirst correctedFinal := by
  have factorNonnegative : 0 ≤ max 1 ((‖transverse first‖ + ‖transverse final‖) / weight) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have transverseBound := mul_le_mul_of_nonneg_right
    (le_max_left 1 ((‖transverse first‖ + ‖transverse final‖) / weight))
    (norm_nonneg (transverse (first - final)))
  have neutralBound := mul_le_mul_of_nonneg_right
    ((div_le_iff₀ weightPositive).mp (le_max_right 1 ((‖transverse first‖ + ‖transverse final‖) / weight)))
    (norm_nonneg (neutral (first - final)))
  have shapeBound : ‖transverse (first - final)‖ +
      (‖transverse first‖ + ‖transverse final‖) * ‖neutral (first - final)‖ ≤
      max 1 ((‖transverse first‖ + ‖transverse final‖) / weight) *
        weightedProjectionDistance transverse neutral weight first final := by
    convert add_le_add transverseBound neutralBound using 1 <;> dsimp only [weightedProjectionDistance] <;> ring
  rw [map_sub, map_sub] at shapeBound
  exact shapeBound.trans ((mul_le_mul_of_nonneg_left inverse factorNonnegative).trans_eq (by ring))

end EulerNonuniqueness.General
