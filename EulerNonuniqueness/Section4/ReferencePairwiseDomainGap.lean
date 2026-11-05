import EulerNonuniqueness.Section4.ReferenceDomainInteractionGap

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem Scales.foreign_moving_point_separation (scales : Scales) {receiver source : ℕ}
    (different : receiver ≠ source) {receiverCenter sourceCenter first second : ℂ}
    (centerGap : |scales.location receiver - scales.location source| / 2 ≤ ‖receiverCenter - sourceCenter‖)
    (receiverControl : ‖first - receiverCenter‖ ≤ scales.location receiver / 16)
    (sourceControl : ‖second - sourceCenter‖ ≤ scales.location source / 16) :
    |scales.location receiver - scales.location source| / 8 ≤ ‖first - second‖ := by
  have locations := scales.location_sum_le_three_distance different
  have triangle := norm_add_le (receiverCenter - first) (first - second)
  have last := norm_add_le (receiverCenter - second) (second - sourceCenter)
  rw [sub_add_sub_cancel, norm_sub_rev receiverCenter first] at triangle
  rw [sub_add_sub_cancel] at last
  linarith [abs_nonneg (scales.location receiver - scales.location source)]

theorem reference_centroid_moving_offset_bound {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (differenceUpper : diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (lengthSmall : scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 100)
    (patch : Fin 4) :
    ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤
      scales.location (index.val + 1) / 16 := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have differencePositive : 0 < diagonalDifference motion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le differenceLower
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape (scales.length_pos _)
    differencePositive differenceUpper ((le_abs_self _).trans radialSmall)
  have bound := patchCentroid_distance_le_of_halfDiagonals positiveBound negativeBound asymmetrySmall patch
  linarith [scales.location_pos (index.val + 1)]

theorem FinitePatchEvolution.reference_domain_moving_offset_bound {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (differenceUpper : diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (lengthSmall : scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 100)
    (boundaryControl : ∀ patch, BoundaryCloseToCircle scales motion time index patch error)
    (radiusPositive : 0 < scales.radius (index.val + 1))
    (radiusSmall : scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 32)
    (patch : Fin 4) (position : ℂ) (member : position ∈ motion.domain time index patch) :
    ‖position - quadrupoleCenter motion time index‖ ≤ scales.location (index.val + 1) / 16 := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have differencePositive : 0 < diagonalDifference motion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le differenceLower
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape (scales.length_pos _)
    differencePositive differenceUpper ((le_abs_self _).trans radialSmall)
  have centerControl : ‖quadrupoleCenter motion time index - quadrupoleCenter motion time index‖ ≤ (0 : ℝ) := by simp
  have bound := evolution.reference_domain_confinement inside index boundaryControl radiusPositive
    positiveBound negativeBound asymmetrySmall centerControl patch position member
  linarith [scales.location_pos (index.val + 1)]

theorem FinitePatchEvolution.reference_pairwise_domain_interaction_gap {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (differenceLower : ∀ index : Fin count, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (differenceUpper : ∀ index : Fin count, diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ index, |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ index, ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter motion time receiver - quadrupoleCenter motion time source‖)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 100)
    (boundaryControl : ∀ index patch, BoundaryCloseToCircle scales motion time index patch error)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 32)
    (receiver source : Fin count) (first second : Fin 4)
    (different : finProdFinEquiv (receiver, first) ≠ finProdFinEquiv (source, second))
    (position : ℂ) (member : position ∈ motion.domain time source second) :
    scales.individualInteractionDistance (receiver.val + 1) (source.val + 1) ≤
      ‖patchCentroid motion time receiver first - position‖ := by
  by_cases same : source = receiver
  · subst source
    rw [Scales.individualInteractionDistance, if_pos rfl]
    exact evolution.reference_sibling_domain_separation inside receiver (differenceLower receiver)
      (radialSmall receiver) (asymmetrySmall receiver) first second
      (fun equality => different (congrArg finProdFinEquiv (Prod.ext rfl equality)))
      (boundaryControl receiver second) (radiusPositive receiver) (radiusSmall receiver) position member
  · rw [Scales.individualInteractionDistance,
      if_neg (fun equality => same (Fin.ext (Nat.add_right_cancel equality)))]
    have indexDifferent : receiver.val + 1 ≠ source.val + 1 :=
      fun equality => same (Fin.ext (Nat.add_right_cancel equality).symm)
    exact scales.foreign_moving_point_separation indexDifferent (centerSeparation receiver source (Ne.symm same))
      (reference_centroid_moving_offset_bound scales motion time receiver (differenceLower receiver)
        (differenceUpper receiver) (radialSmall receiver) (asymmetrySmall receiver) (lengthSmall receiver) first)
      (evolution.reference_domain_moving_offset_bound inside source (differenceLower source) (differenceUpper source)
        (radialSmall source) (asymmetrySmall source) (lengthSmall source) (boundaryControl source)
        (radiusPositive source) (radiusSmall source) second position member)

end EulerNonuniqueness.Paper
