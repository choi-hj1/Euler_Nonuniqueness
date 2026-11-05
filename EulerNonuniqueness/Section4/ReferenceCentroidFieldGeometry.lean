import EulerNonuniqueness.Section4.ReferencePairwiseDomainGap

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

def referenceSourceDistance {count : ℕ} (scales : Scales) (receiver source : Fin count) : ℝ :=
  |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8

structure ReferenceCentroidFieldGeometry {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : Prop where
  internalSeparated : ∀ receiver source : Fin 4, source ≠ receiver →
    scales.length (index.val + 1) / 100 ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time index source‖
  internalRadius : 8 * scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 100
  positive : ∀ source ∈ Finset.univ.erase index, 0 < referenceSourceDistance scales index source
  sourceBounded : ∀ source ∈ Finset.univ.erase index, ∀ patch,
    motion.domain time source patch ⊆ Metric.closedBall (patchCentroid motion time source patch) (2 * scales.radius (source.val + 1))
  receiverSmall : ∀ source ∈ Finset.univ.erase index,
    8 * scales.radius (index.val + 1) ≤ referenceSourceDistance scales index source
  sourceSmall : ∀ source ∈ Finset.univ.erase index,
    4 * scales.radius (source.val + 1) ≤ referenceSourceDistance scales index source
  centroidsSeparated : ∀ receiver source, source ∈ Finset.univ.erase index → ∀ patch,
    referenceSourceDistance scales index source ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖
  centroidsBounded : ∀ patch,
    ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ 3 * scales.length (index.val + 1)
  centerSeparated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
    referenceSourceDistance scales index source ≤ ‖quadrupoleCenter motion time index - location‖
  near : ∀ source ∈ Finset.univ.erase index,
    2 * (3 * scales.length (index.val + 1)) ≤ referenceSourceDistance scales index source

theorem FinitePatchEvolution.reference_centroid_field_geometry
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
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
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (deformation : Fin count → ℝ)
    (control : ∀ index patch, BoundaryCloseToCircle scales motion time index patch (deformation index))
    (nonnegative : ∀ index, 0 ≤ deformation index) (small : ∀ index, deformation index ≤ 1 / 16)
    (index : Fin count) : ReferenceCentroidFieldGeometry scales motion time index := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have radiusPositive (source : Fin count) := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (source.val + 1)
  have lengthWeaker (source : Fin count) : scales.length (source.val + 1) ≤ scales.location (source.val + 1) / 100 := by
    linarith [lengthSmall source, scales.location_pos (source.val + 1)]
  have domainRadius (source : Fin count) : scales.radius (source.val + 1) * (1 + deformation source) ≤
      scales.length (source.val + 1) / 32 := by
    have coefficient := mul_le_mul_of_nonneg_left (small source) (radiusPositive source).le
    linarith [radiusSmall source, scales.length_pos (source.val + 1)]
  have centroidOffset (source : Fin count) (patch : Fin 4) :=
    reference_centroid_moving_offset_bound scales motion time source (differenceLower source) (differenceUpper source)
      (radialSmall source) (asymmetrySmall source) (lengthWeaker source) patch
  have indexDifferent (source : Fin count) (member : source ∈ Finset.univ.erase index) :
      index.val + 1 ≠ source.val + 1 :=
    fun equality => (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro receiver source different
    have separation := patchCentroid_pair_lower_of_reference_shape motion time index lengthPositive
      (differenceLower index) (radialSmall index) (asymmetrySmall index) receiver source (Ne.symm different)
    linarith
  · linarith [radiusSmall index]
  · intro source member
    exact div_pos (scales.location_distance_pos (indexDifferent source member)) (by norm_num)
  · intro source member patch position positionInside
    have bounded := evolution.domain_subset_centroid_ball inside source patch (control source patch) (radiusPositive source) positionInside
    have normBound : ‖position - patchCentroid motion time source patch‖ ≤ scales.radius (source.val + 1) * (1 + deformation source) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using bounded
    have coefficient := mul_le_mul_of_nonneg_left (small source) (radiusPositive source).le
    have finalBound : ‖position - patchCentroid motion time source patch‖ ≤ 2 * scales.radius (source.val + 1) := by
      nlinarith only [normBound, coefficient, (radiusPositive source).le]
    simpa only [Metric.mem_closedBall, dist_eq_norm] using finalBound
  · intro source member
    have locations := scales.location_sum_le_three_distance (indexDifferent source member)
    dsimp only [referenceSourceDistance]
    linarith [radiusSmall index, lengthSmall index, scales.location_pos (source.val + 1)]
  · intro source member
    have locations := scales.location_sum_le_three_distance (indexDifferent source member)
    dsimp only [referenceSourceDistance]
    linarith only [radiusSmall source, lengthSmall source, scales.location_pos (index.val + 1), locations,
      abs_nonneg (scales.location (index.val + 1) - scales.location (source.val + 1))]
  · intro receiver source member patch
    exact scales.foreign_moving_point_separation (indexDifferent source member)
      (centerSeparation index source (Ne.symm (Finset.mem_erase.mp member).1))
      (centroidOffset index receiver) (centroidOffset source patch)
  · intro patch
    have differencePositive : 0 < diagonalDifference motion time index :=
      (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le (differenceLower index)
    obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape lengthPositive differencePositive
      (differenceUpper index) ((le_abs_self _).trans (radialSmall index))
    have estimate := patchCentroid_distance_le_of_halfDiagonals positiveBound negativeBound (asymmetrySmall index) patch
    linarith
  · intro source member patch location locationInside
    exact scales.foreign_moving_point_separation (indexDifferent source member)
      (centerSeparation index source (Ne.symm (Finset.mem_erase.mp member).1))
      (show ‖quadrupoleCenter motion time index - quadrupoleCenter motion time index‖ ≤ scales.location (index.val + 1) / 16 by
        rw [sub_self, norm_zero]; exact div_nonneg (scales.location_pos (index.val + 1)).le (by norm_num))
      (evolution.reference_domain_moving_offset_bound inside source (differenceLower source) (differenceUpper source)
        (radialSmall source) (asymmetrySmall source) (lengthWeaker source) (control source)
        (radiusPositive source) (domainRadius source) patch location locationInside)
  · intro source member
    have locations := scales.location_sum_le_three_distance (indexDifferent source member)
    dsimp only [referenceSourceDistance]
    linarith [lengthSmall index, scales.location_pos (source.val + 1)]

end EulerNonuniqueness.Paper
