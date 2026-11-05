import EulerNonuniqueness.Section6.PaperDiagonalInternalForcingSplit
import EulerNonuniqueness.Section6.FourPointDilationRelativeForcing
import EulerNonuniqueness.Section6.PaperRelativeNeutralExternal

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointDilationDirectionalRate_velocity_add
    (positions first second : FourPointConfiguration) :
    fourPointDilationDirectionalRate positions (first + second) =
      fourPointDilationDirectionalRate positions first + fourPointDilationDirectionalRate positions second := by
  have odd : fourPointOddPart (first + second) = fourPointOddPart first + fourPointOddPart second := by
    ext <;> simp only [fourPointOddPart, Pi.add_apply, Prod.fst_add, Prod.snd_add] <;> ring
  simp only [fourPointDilationDirectionalRate, odd, Prod.fst_add, Prod.snd_add, inner_add_right]
  ring

theorem fourPointDilationDirectionalRate_velocity_centered
    (positions velocity : FourPointConfiguration) (center : ℂ) :
    fourPointDilationDirectionalRate positions (fun patch => velocity patch - center) =
      fourPointDilationDirectionalRate positions velocity := by
  have odd : fourPointOddPart (fun patch => velocity patch - center) = fourPointOddPart velocity := by
    change fourPointOddPart (velocity - fun _ => center) = _
    rw [fourPointOddPart_sub, fourPointOddPart_constant, sub_zero]
  simp only [fourPointDilationDirectionalRate, odd]

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def quadrupoleDilationPatchError {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : FourPointConfiguration :=
  fun patch => quadrupoleInternalPatchResidual scales motion time index patch +
    quadrupoleExternalReceiverResidual scales motion time index patch

def quadrupoleExternalDilationRate {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℝ :=
  fourPointDilationDirectionalRate (fun patch => patchCentroid motion time index patch)
    (quadrupoleCenteredExternalIncrement scales motion index time)

def quadrupolePatchDilationRate {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℝ :=
  fourPointDilationDirectionalRate (fun patch => patchCentroid motion time index patch)
    (quadrupoleDilationPatchError scales motion index time)

theorem diagonalOddForcingRate_eq_internal_external_patch
    {count : ℕ} (scales : Scales) (motion : PatchMotion count) (index : Fin count) (time : ℝ)
    (noncollision : FourPointNoncollision (fun patch => patchCentroid motion time index patch))
    (centralNoncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index))) :
    diagonalOddForcingRate scales motion index time =
      quadrupoleInternalDilationRate scales motion index time +
        quadrupoleExternalDilationRate scales motion index time + quadrupolePatchDilationRate scales motion index time := by
  let positions : FourPointConfiguration := fun patch => patchCentroid motion time index patch
  let fieldValues : FourPointConfiguration := fun patch =>
    biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index patch)
  have identity : quadrupoleCentroidForcing scales motion time index =
      fieldValues + quadrupoleDilationPatchError scales motion index time := by
    funext patch
    simp only [quadrupoleCentroidForcing, fieldValues, quadrupoleDilationPatchError, Pi.add_apply]
    abel
  have centered := fourPointDilationDirectionalRate_velocity_centered positions fieldValues
    (biotSavart (externalPatchVorticity scales motion time index) (quadrupoleCenter motion time index))
  rw [diagonalOddForcingRate_eq_internal_directional scales motion index time noncollision centralNoncollision,
    identity, fourPointDilationDirectionalRate_velocity_add]
  change quadrupoleInternalDilationRate scales motion index time +
      (fourPointDilationDirectionalRate positions fieldValues + quadrupolePatchDilationRate scales motion index time) = _
  change quadrupoleExternalDilationRate scales motion index time =
    fourPointDilationDirectionalRate positions fieldValues at centered
  rw [← centered]
  ring

theorem quadrupole_patch_dilation_rate_relative_bound
    {count : ℕ} (scales : Scales) (first second : PatchMotion count) (index : Fin count) (time : ℝ)
    {radiusFactor : ℝ} (radiusNonnegative : 0 ≤ radiusFactor)
    (extent : ∀ patch, ‖patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤
      radiusFactor * scales.length (index.val + 1)) :
    |quadrupolePatchDilationRate scales first index time - quadrupolePatchDilationRate scales second index time| /
        scales.length (index.val + 1) ^ 2 ≤
      4 * (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
          scales.length (index.val + 1)) * (‖quadrupoleDilationPatchError scales second index time‖ / scales.length (index.val + 1)) +
      4 * radiusFactor * (‖quadrupoleDilationPatchError scales first index time -
        quadrupoleDilationPatchError scales second index time‖ / scales.length (index.val + 1)) := by
  let firstCentered : FourPointConfiguration := fun patch => patchCentroid first time index patch - quadrupoleCenter first time index
  let secondCentered : FourPointConfiguration := fun patch => patchCentroid second time index patch - quadrupoleCenter second time index
  have lengthPositive := scales.length_pos (index.val + 1)
  have firstBound : ‖firstCentered‖ ≤ radiusFactor * scales.length (index.val + 1) :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg radiusNonnegative lengthPositive.le)).mpr extent
  have actual := fourPointDilationDirectionalRate_relative_norm_le firstCentered secondCentered
    (quadrupoleDilationPatchError scales first index time) (quadrupoleDilationPatchError scales second index time)
  rw [fourPointDilationDirectionalRate_centered, fourPointDilationDirectionalRate_centered] at actual
  have enlarged := actual.trans (add_le_add_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left firstBound (by norm_num : (0 : ℝ) ≤ 4))
      (norm_nonneg (quadrupoleDilationPatchError scales first index time - quadrupoleDilationPatchError scales second index time))) _)
  apply (div_le_div_of_nonneg_right enlarged (sq_nonneg (scales.length (index.val + 1)))).trans_eq
  dsimp only [firstCentered, secondCentered, quadrupolePatchDilationRate]
  field_simp [lengthPositive.ne']
  <;> ring

end EulerNonuniqueness.Paper
