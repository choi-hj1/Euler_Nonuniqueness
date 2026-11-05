import EulerNonuniqueness.Section4.ReferenceSiblingSeparation
import EulerNonuniqueness.Section1.IndividualPatchInteractionWeight
import EulerNonuniqueness.Section3.BoundaryDomainConfinement

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem reference_sibling_center_gap {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) {length sourceRadius : ℝ}
    (lengthPositive : 0 < length)
    (differenceLower : length ^ 2 / 2 ≤ diagonalDifference motion time index)
    (radialSmall : |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry motion time index‖ ≤ length / 64)
    (radiusSmall : sourceRadius ≤ length / 100)
    (first second : Fin 4) (different : first ≠ second) :
    length / 100 + 3 * sourceRadius ≤
      ‖patchCentroid motion time index first - patchCentroid motion time index second‖ := by
  have actual := patchCentroid_pair_lower_of_reference_shape motion time index lengthPositive
    differenceLower radialSmall asymmetrySmall first second different
  linarith

theorem FinitePatchEvolution.reference_sibling_domain_separation {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time error : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (radialSmall : |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (first second : Fin 4) (different : first ≠ second)
    (sourceControl : BoundaryCloseToCircle scales motion time index second error)
    (radiusPositive : 0 < scales.radius (index.val + 1))
    (radiusSmall : scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 32)
    (position : ℂ) (member : position ∈ motion.domain time index second) :
    scales.length (index.val + 1) / 100 ≤ ‖patchCentroid motion time index first - position‖ := by
  have pairBound := patchCentroid_pair_lower_of_reference_shape motion time index (scales.length_pos _)
    differenceLower radialSmall asymmetrySmall first second different
  have domainBound := evolution.domain_subset_centroid_ball inside index second sourceControl radiusPositive member
  rw [Metric.mem_closedBall, dist_eq_norm] at domainBound
  have triangle : ‖patchCentroid motion time index first - patchCentroid motion time index second‖ ≤
      ‖patchCentroid motion time index first - position‖ + ‖position - patchCentroid motion time index second‖ := by
    calc
      _ = ‖(patchCentroid motion time index first - position) +
          (position - patchCentroid motion time index second)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  linarith [scales.length_pos (index.val + 1)]

theorem Scales.foreign_point_separation (scales : Scales) {receiver source : ℕ}
    (different : receiver ≠ source) {center position : ℂ}
    (receiverControl : ‖center - (scales.location receiver : ℂ)‖ ≤ scales.location receiver / 16)
    (sourceControl : ‖position - (scales.location source : ℂ)‖ ≤ scales.location source / 16) :
    |scales.location receiver - scales.location source| / 8 ≤ ‖center - position‖ := by
  have locations := scales.location_sum_le_three_distance different
  have triangle : |scales.location receiver - scales.location source| ≤
      ‖center - (scales.location receiver : ℂ)‖ + ‖center - position‖ +
        ‖position - (scales.location source : ℂ)‖ := by
    calc
      _ = ‖((scales.location receiver : ℂ) - center) + (center - position) +
          (position - (scales.location source : ℂ))‖ := by
        rw [sub_add_sub_cancel, sub_add_sub_cancel, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := (norm_add_le _ _).trans
        (add_le_add_right ((norm_add_le _ _).trans (by rw [norm_sub_rev])) _)
  linarith [abs_nonneg (scales.location receiver - scales.location source)]

end EulerNonuniqueness.Paper
