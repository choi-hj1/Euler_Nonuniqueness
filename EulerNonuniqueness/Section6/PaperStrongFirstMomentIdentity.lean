import EulerNonuniqueness.Section5.CascadeRelativeFirstMomentHistory
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing
import EulerNonuniqueness.Section6.FourPointInversePowerRelative

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem fourPointSignedMoment_difference_norm_eq_strong_firstMoment
    {count : ℕ} (scales : Scales) (first second : PatchMotion count) (index : Fin count) (time : ℝ)
    (firstCenter secondCenter : ℂ) :
    ‖fourPointSignedMoment (fun patch => patchCentroid first time index patch - firstCenter) -
        fourPointSignedMoment (fun patch => patchCentroid second time index patch - secondCenter)‖ =
      (scales.length (index.val + 1) ^ 2 / scales.location (index.val + 1)) *
        ‖relativeNormalizedFirstMoment scales first second index time‖ := by
  rw [fourPointSignedMoment_centered, fourPointSignedMoment_centered,
    centroid_fourPointSignedMoment, centroid_fourPointSignedMoment, ← mul_sub]
  have coefficientPositive : 0 < 4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2 := by
    exact div_pos (mul_pos (by norm_num) (scales.location_pos _)) (sq_pos_of_pos (scales.length_pos _))
  simp only [relativeNormalizedFirstMoment, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos coefficientPositive]
  norm_num
  field_simp [(scales.location_pos (index.val + 1)).ne', (scales.length_pos (index.val + 1)).ne']
  <;> ring

theorem quadrupoleCenteredPositionDifference_sum_le_array_norm
    {count : ℕ} (first second : PatchMotion count) (index : Fin count) (time : ℝ) :
    (∑ patch : Fin 4, ‖(patchCentroid first time index patch - quadrupoleCenter first time index) -
      (patchCentroid second time index patch - quadrupoleCenter second time index)‖) ≤
      4 * ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ := by
  have actual := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) =>
    norm_le_pi_norm ((fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
      (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)) patch)
  simpa only [Pi.sub_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using actual

end EulerNonuniqueness.Paper
