import EulerNonuniqueness.Section6.PaperDilationForcingParts

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem quadrupole_external_dilation_rate_relative_bound
    {count : ℕ} (scales : Scales) (first second : PatchMotion count) (index : Fin count) (time : ℝ)
    {radiusFactor : ℝ} (radiusNonnegative : 0 ≤ radiusFactor)
    (extent : ∀ patch, ‖patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤
      radiusFactor * scales.length (index.val + 1)) :
    |quadrupoleExternalDilationRate scales first index time - quadrupoleExternalDilationRate scales second index time| /
        scales.length (index.val + 1) ^ 2 ≤
      4 * (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
          scales.length (index.val + 1)) * (‖quadrupoleCenteredExternalIncrement scales second index time‖ / scales.length (index.val + 1)) +
      4 * radiusFactor * (‖quadrupoleCenteredExternalIncrement scales first index time -
        quadrupoleCenteredExternalIncrement scales second index time‖ / scales.length (index.val + 1)) := by
  let firstCentered : FourPointConfiguration := fun patch => patchCentroid first time index patch - quadrupoleCenter first time index
  let secondCentered : FourPointConfiguration := fun patch => patchCentroid second time index patch - quadrupoleCenter second time index
  have lengthPositive := scales.length_pos (index.val + 1)
  have firstBound : ‖firstCentered‖ ≤ radiusFactor * scales.length (index.val + 1) :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg radiusNonnegative lengthPositive.le)).mpr extent
  have actual := fourPointDilationDirectionalRate_relative_norm_le firstCentered secondCentered
    (quadrupoleCenteredExternalIncrement scales first index time) (quadrupoleCenteredExternalIncrement scales second index time)
  rw [fourPointDilationDirectionalRate_centered, fourPointDilationDirectionalRate_centered] at actual
  have enlarged := actual.trans (add_le_add_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left firstBound (by norm_num : (0 : ℝ) ≤ 4))
      (norm_nonneg (quadrupoleCenteredExternalIncrement scales first index time - quadrupoleCenteredExternalIncrement scales second index time))) _)
  apply (div_le_div_of_nonneg_right enlarged (sq_nonneg (scales.length (index.val + 1)))).trans_eq
  dsimp only [firstCentered, secondCentered, quadrupoleExternalDilationRate]
  field_simp [lengthPositive.ne']
  <;> ring


end EulerNonuniqueness.Paper

