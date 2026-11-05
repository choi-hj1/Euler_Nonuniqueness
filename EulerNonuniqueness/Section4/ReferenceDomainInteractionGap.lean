import EulerNonuniqueness.Section4.ReferencePatchDomainSeparation
import EulerNonuniqueness.Section4.ReferenceConfinement

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem reference_centroid_location_bound {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (differenceUpper : diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSmall : ‖quadrupoleCenter motion time index - (scales.location (index.val + 1) : ℂ)‖ ≤
      scales.location (index.val + 1) / 100)
    (lengthSmall : scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 100)
    (patch : Fin 4) :
    ‖patchCentroid motion time index patch - (scales.location (index.val + 1) : ℂ)‖ ≤
      scales.location (index.val + 1) / 16 := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have differencePositive : 0 < diagonalDifference motion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le differenceLower
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape (scales.length_pos _)
    differencePositive differenceUpper (le_trans (le_abs_self _) radialSmall)
  have centroidBound := patchCentroid_distance_le_of_halfDiagonals positiveBound negativeBound asymmetrySmall patch
  have triangle : ‖patchCentroid motion time index patch - (scales.location (index.val + 1) : ℂ)‖ ≤
      ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ +
        ‖quadrupoleCenter motion time index - (scales.location (index.val + 1) : ℂ)‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  linarith [scales.location_pos (index.val + 1)]

theorem FinitePatchEvolution.reference_domain_location_bound {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (differenceUpper : diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSmall : ‖quadrupoleCenter motion time index - (scales.location (index.val + 1) : ℂ)‖ ≤
      scales.location (index.val + 1) / 100)
    (lengthSmall : scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 100)
    (boundaryControl : ∀ patch, BoundaryCloseToCircle scales motion time index patch error)
    (radiusPositive : 0 < scales.radius (index.val + 1))
    (radiusSmall : scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 32)
    (patch : Fin 4) (position : ℂ) (member : position ∈ motion.domain time index patch) :
    ‖position - (scales.location (index.val + 1) : ℂ)‖ ≤ scales.location (index.val + 1) / 16 := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have differencePositive : 0 < diagonalDifference motion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le differenceLower
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape (scales.length_pos _)
    differencePositive differenceUpper (le_trans (le_abs_self _) radialSmall)
  have bound := evolution.reference_domain_confinement inside index boundaryControl radiusPositive
    positiveBound negativeBound asymmetrySmall centerSmall patch position member
  linarith [scales.location_pos (index.val + 1)]

theorem FinitePatchEvolution.reference_domain_interaction_gap {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (differenceLower : ∀ index : Fin count,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (differenceUpper : ∀ index : Fin count,
      diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ index, |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ index, ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSmall : ∀ index, ‖quadrupoleCenter motion time index - (scales.location (index.val + 1) : ℂ)‖ ≤
      scales.location (index.val + 1) / 100)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 100)
    (boundaryControl : ∀ index patch, BoundaryCloseToCircle scales motion time index patch error)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 32)
    (receiver source : Fin count) (first second : Fin 4)
    (different : finProdFinEquiv (receiver, first) ≠ finProdFinEquiv (source, second))
    (position : ℂ) (member : position ∈ motion.domain time source second) :
    scales.individualInteractionDistance (receiver.val + 1) (source.val + 1) ≤
      ‖patchCentroid motion time receiver first - position‖ := by
  by_cases same : source = receiver
  · subst source
    rw [Scales.individualInteractionDistance, if_pos rfl]
    apply evolution.reference_sibling_domain_separation inside receiver (differenceLower receiver)
      (radialSmall receiver) (asymmetrySmall receiver) first second
      (fun equality => different (congrArg finProdFinEquiv (Prod.ext rfl equality)))
      (boundaryControl receiver second) (radiusPositive receiver) (radiusSmall receiver) position member
  · rw [Scales.individualInteractionDistance,
      if_neg (fun equality => same (Fin.ext (Nat.add_right_cancel equality)))]
    exact scales.foreign_point_separation
      (fun equality => same (Fin.ext (Nat.add_right_cancel equality).symm))
      (reference_centroid_location_bound scales motion time receiver (differenceLower receiver)
        (differenceUpper receiver) (radialSmall receiver) (asymmetrySmall receiver) (centerSmall receiver)
        (lengthSmall receiver) first)
      (evolution.reference_domain_location_bound inside source (differenceLower source) (differenceUpper source)
        (radialSmall source) (asymmetrySmall source) (centerSmall source) (lengthSmall source)
        (boundaryControl source) (radiusPositive source) (radiusSmall source) second position member)

end EulerNonuniqueness.Paper
