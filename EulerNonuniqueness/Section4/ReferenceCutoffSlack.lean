import EulerNonuniqueness.Section4.ReferencePairwiseDomainGap
import EulerNonuniqueness.Section4.InitialReferenceDiskSeparation

noncomputable section

namespace EulerNonuniqueness.Paper

def referencePairCutoffSlack {count : ℕ} (scales : Scales) (first second : Fin count × Fin 4) : ℝ :=
  if first.1 = second.1 then scales.length (first.1.val + 1) / 128
  else |scales.location (first.1.val + 1) - scales.location (second.1.val + 1)| / 64

theorem referencePairCutoffSlack_pos {count : ℕ} (scales : Scales) (first second : Fin count × Fin 4) :
    0 < referencePairCutoffSlack scales first second := by
  unfold referencePairCutoffSlack
  split_ifs with same
  · exact div_pos (scales.length_pos _) (by norm_num)
  · exact div_pos (scales.location_distance_pos
      (fun equality => same (Fin.ext (Nat.add_right_cancel equality)))) (by norm_num)

theorem reference_centroid_pair_cutoff_slack {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ)
    (differenceLower : ∀ index : Fin count, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (differenceUpper : ∀ index : Fin count, diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ index, |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ index, ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter motion time receiver - quadrupoleCenter motion time source‖)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (first second : Fin count × Fin 4) (different : first ≠ second) :
    3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) +
        4 * referencePairCutoffSlack scales first second ≤
      ‖patchCentroid motion time first.1 first.2 - patchCentroid motion time second.1 second.2‖ := by
  rcases first with ⟨firstIndex, firstPatch⟩
  rcases second with ⟨secondIndex, secondPatch⟩
  by_cases same : firstIndex = secondIndex
  · subst secondIndex
    have patchDifferent : firstPatch ≠ secondPatch := fun equality => different (Prod.ext rfl equality)
    have separation := patchCentroid_pair_lower_of_reference_shape motion time firstIndex (scales.length_pos _)
      (differenceLower firstIndex) (radialSmall firstIndex) (asymmetrySmall firstIndex) firstPatch secondPatch patchDifferent
    simp only [referencePairCutoffSlack, Prod.fst, ite_true]
    linarith [radiusSmall firstIndex, scales.length_pos (firstIndex.val + 1)]
  · have lengthWeaker (index : Fin count) : scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 100 := by
      linarith [lengthSmall index, scales.location_pos (index.val + 1)]
    have separation := scales.foreign_moving_point_separation
      (show firstIndex.val + 1 ≠ secondIndex.val + 1 from fun equality => same (Fin.ext (Nat.add_right_cancel equality)))
      (centerSeparation firstIndex secondIndex same)
      (reference_centroid_moving_offset_bound scales motion time firstIndex (differenceLower firstIndex)
        (differenceUpper firstIndex) (radialSmall firstIndex) (asymmetrySmall firstIndex) (lengthWeaker firstIndex) firstPatch)
      (reference_centroid_moving_offset_bound scales motion time secondIndex (differenceLower secondIndex)
        (differenceUpper secondIndex) (radialSmall secondIndex) (asymmetrySmall secondIndex) (lengthWeaker secondIndex) secondPatch)
    have locations := scales.location_sum_le_three_distance
      (show firstIndex.val + 1 ≠ secondIndex.val + 1 from fun equality => same (Fin.ext (Nat.add_right_cancel equality)))
    simp only [referencePairCutoffSlack, if_neg same]
    linarith [radiusSmall firstIndex, radiusSmall secondIndex, lengthSmall firstIndex, lengthSmall secondIndex,
      abs_nonneg (scales.location (firstIndex.val + 1) - scales.location (secondIndex.val + 1))]

theorem reference_initial_pair_cutoff_slack {count : ℕ} (scales : Scales)
    (phase unstable : Fin count → ℝ) (small : ∀ index, |unstable index| ≤ 1 / 2)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (first second : Fin count × Fin 4) (different : first ≠ second) :
    3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) +
        4 * referencePairCutoffSlack scales first second ≤
      ‖initialDiskCenter scales (first.1.val + 1) (phase first.1) (unstable first.1) first.2 -
        initialDiskCenter scales (second.1.val + 1) (phase second.1) (unstable second.1) second.2‖ := by
  rcases first with ⟨firstIndex, firstPatch⟩
  rcases second with ⟨secondIndex, secondPatch⟩
  by_cases same : firstIndex = secondIndex
  · subst secondIndex
    have patchDifferent : firstPatch ≠ secondPatch := fun equality => different (Prod.ext rfl equality)
    have separation := initialDiskCenter_same_scale_separation scales (firstIndex.val + 1) (phase firstIndex)
      (unstable firstIndex) (small firstIndex) firstPatch secondPatch patchDifferent
    simp only [referencePairCutoffSlack, Prod.fst, ite_true]
    linarith [radiusSmall firstIndex, scales.length_pos (firstIndex.val + 1)]
  · have indicesDifferent : firstIndex.val + 1 ≠ secondIndex.val + 1 :=
      fun equality => same (Fin.ext (Nat.add_right_cancel equality))
    have locations := scales.location_sum_le_three_distance indicesDifferent
    have firstOffset := initialDiskCenter_offset_bound scales (firstIndex.val + 1) (phase firstIndex)
      (unstable firstIndex) (small firstIndex) firstPatch
    have secondOffset := initialDiskCenter_offset_bound scales (secondIndex.val + 1) (phase secondIndex)
      (unstable secondIndex) (small secondIndex) secondPatch
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (scales.location (firstIndex.val + 1) : ℂ)
      (initialDiskCenter scales (firstIndex.val + 1) (phase firstIndex) (unstable firstIndex) firstPatch)
      (scales.location (secondIndex.val + 1) : ℂ)
    have last := norm_sub_le_norm_sub_add_norm_sub
      (initialDiskCenter scales (firstIndex.val + 1) (phase firstIndex) (unstable firstIndex) firstPatch)
      (initialDiskCenter scales (secondIndex.val + 1) (phase secondIndex) (unstable secondIndex) secondPatch)
      (scales.location (secondIndex.val + 1) : ℂ)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      norm_sub_rev (scales.location (firstIndex.val + 1) : ℂ)] at triangle
    simp only [referencePairCutoffSlack, if_neg same]
    linarith [radiusSmall firstIndex, radiusSmall secondIndex, lengthSmall firstIndex, lengthSmall secondIndex,
      abs_nonneg (scales.location (firstIndex.val + 1) - scales.location (secondIndex.val + 1))]

end EulerNonuniqueness.Paper
