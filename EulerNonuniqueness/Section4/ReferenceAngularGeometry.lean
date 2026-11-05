import EulerNonuniqueness.Section4.ReferencePairwiseDomainGap

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.reference_angular_geometry
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (differenceLower : ∀ index : Fin count, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (differenceUpper : ∀ index : Fin count, diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ index, |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ index, ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter motion time receiver - quadrupoleCenter motion time source‖)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (control : ∀ index patch, BoundaryCloseToCircle scales motion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16)
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 1000)
    (index : Fin count) :
    (∀ patch, motion.domain time index patch ⊆
      Metric.closedBall (quadrupoleCenter motion time index) (3 * scales.length (index.val + 1))) ∧
    (∀ receiver source : Fin 4, source ≠ receiver → ∀ position ∈ motion.domain time index receiver,
      ∀ location ∈ motion.domain time index source, scales.length (index.val + 1) / 200 ≤ ‖position - location‖) ∧
    (∀ position ∈ Metric.closedBall (quadrupoleCenter motion time index) (3 * scales.length (index.val + 1)),
      ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 ≤ ‖position - location‖) := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have lengthWeaker (source : Fin count) : scales.length (source.val + 1) ≤ scales.location (source.val + 1) / 100 := by
    linarith [lengthSmall source, scales.location_pos (source.val + 1)]
  have radiusWeaker (source : Fin count) :
      scales.radius (source.val + 1) * (1 + error) ≤ scales.length (source.val + 1) / 32 := by
    linarith [radiusSmall source, scales.length_pos (source.val + 1)]
  have radiusPositive (source : Fin count) := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (source.val + 1)
  have differencePositive : 0 < diagonalDifference motion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le (differenceLower index)
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape lengthPositive differencePositive
    (differenceUpper index) ((le_abs_self _).trans (radialSmall index))
  refine ⟨?_, ?_, ?_⟩
  · intro patch position member
    have estimate := evolution.reference_domain_confinement inside index (control index) (radiusPositive index)
      positiveBound negativeBound (asymmetrySmall index)
      (show ‖quadrupoleCenter motion time index - quadrupoleCenter motion time index‖ ≤ (0 : ℝ) by simp)
      patch position member
    have normBound : ‖position - quadrupoleCenter motion time index‖ ≤ 3 * scales.length (index.val + 1) := by
      linarith [radiusSmall index]
    simpa only [Metric.mem_closedBall, dist_eq_norm] using normBound
  · intro receiver source different position positionInside location locationInside
    have sourceBound := evolution.reference_sibling_domain_separation inside index (differenceLower index)
      (radialSmall index) (asymmetrySmall index) receiver source (Ne.symm different) (control index source)
      (radiusPositive index) (radiusWeaker index) location locationInside
    have receiverBound : ‖position - patchCentroid motion time index receiver‖ ≤
        scales.radius (index.val + 1) * (1 + error) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using
        evolution.domain_subset_centroid_ball inside index receiver (control index receiver)
          (radiusPositive index) positionInside
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (patchCentroid motion time index receiver) position location
    rw [norm_sub_rev (patchCentroid motion time index receiver) position] at triangle
    linarith [radiusSmall index]
  · intro position positionInside source different patch location locationInside
    have positionBound : ‖position - quadrupoleCenter motion time index‖ ≤ scales.location (index.val + 1) / 16 := by
      have normBound : ‖position - quadrupoleCenter motion time index‖ ≤ 3 * scales.length (index.val + 1) := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using positionInside
      linarith [lengthSmall index, scales.location_pos (index.val + 1)]
    exact scales.foreign_moving_point_separation
      (fun equality => (Finset.mem_erase.mp different).1 (Fin.ext (Nat.add_right_cancel equality).symm))
      (centerSeparation index source (Ne.symm (Finset.mem_erase.mp different).1)) positionBound
      (evolution.reference_domain_moving_offset_bound inside source (differenceLower source) (differenceUpper source)
        (radialSmall source) (asymmetrySmall source) (lengthWeaker source) (control source)
        (radiusPositive source) (radiusWeaker source) patch location locationInside)

end EulerNonuniqueness.Paper
