import EulerNonuniqueness.Section3.BoundaryDomainConfinement
import EulerNonuniqueness.Section4.InitialDiskUniformBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem radialShape_eq_unstable_add_stable {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) :
    radialShape motion time index = unstableShape motion time index + stableShape motion time index := by
  unfold unstableShape stableShape
  ring

theorem halfDiagonals_norm_le_of_reference_shape {count : ℕ} {motion : PatchMotion count}
    {time length : ℝ} {index : Fin count} (lengthPositive : 0 < length)
    (differencePositive : 0 < diagonalDifference motion time index)
    (differenceUpper : diagonalDifference motion time index ≤ 2 * length ^ 2)
    (radialUpper : radialShape motion time index ≤ 1 / 2) :
    ‖positiveHalfDiagonal motion time index‖ ≤ 2 * length ∧
      ‖negativeHalfDiagonal motion time index‖ ≤ 2 * length := by
  have positiveSquare : 0 < ‖positiveHalfDiagonal motion time index‖ ^ 2 := by
    dsimp only [diagonalDifference] at differencePositive
    nlinarith [sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  have ratioUpper : ‖negativeHalfDiagonal motion time index‖ ^ 2 /
      ‖positiveHalfDiagonal motion time index‖ ^ 2 ≤ 1 / 2 := by
    have bound := (div_le_iff₀ reference_rhombusRatio_bounds.1).mp radialUpper
    change ‖negativeHalfDiagonal motion time index‖ ^ 2 /
      ‖positiveHalfDiagonal motion time index‖ ^ 2 - rhombusRatio ≤ 1 / 2 * rhombusRatio at bound
    linarith [reference_rhombusRatio_bounds.2]
  have squares := (div_le_iff₀ positiveSquare).mp ratioUpper
  dsimp only [diagonalDifference] at differenceUpper
  constructor <;> nlinarith [norm_nonneg (positiveHalfDiagonal motion time index),
    norm_nonneg (negativeHalfDiagonal motion time index)]

theorem patchCentroid_sub_quadrupoleCenter {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4) :
    patchCentroid motion time index patch - quadrupoleCenter motion time index =
      if patch = 0 then centroidAsymmetry motion time index + positiveHalfDiagonal motion time index
      else if patch = 1 then centroidAsymmetry motion time index - positiveHalfDiagonal motion time index
      else if patch = 2 then -centroidAsymmetry motion time index + negativeHalfDiagonal motion time index
      else -centroidAsymmetry motion time index - negativeHalfDiagonal motion time index := by
  fin_cases patch <;> simp [quadrupoleCenter, centroidAsymmetry, positiveHalfDiagonal,
    negativeHalfDiagonal, Fin.sum_univ_succ] <;> ring

theorem patchCentroid_distance_le_of_halfDiagonals {count : ℕ} {motion : PatchMotion count}
    {time diagonalBound asymmetryBound : ℝ} {index : Fin count}
    (positiveBound : ‖positiveHalfDiagonal motion time index‖ ≤ diagonalBound)
    (negativeBound : ‖negativeHalfDiagonal motion time index‖ ≤ diagonalBound)
    (asymmetryControl : ‖centroidAsymmetry motion time index‖ ≤ asymmetryBound) (patch : Fin 4) :
    ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ asymmetryBound + diagonalBound := by
  rw [patchCentroid_sub_quadrupoleCenter]
  split_ifs
  · exact (norm_add_le _ _).trans (add_le_add asymmetryControl positiveBound)
  · exact (norm_sub_le _ _).trans (add_le_add asymmetryControl positiveBound)
  · exact (norm_add_le _ _).trans (by simpa only [norm_neg] using add_le_add asymmetryControl negativeBound)
  · exact (norm_sub_le _ _).trans (by simpa only [norm_neg] using add_le_add asymmetryControl negativeBound)

theorem FinitePatchEvolution.reference_domain_confinement {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time boundaryError diagonalBound asymmetryBound centerError : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count) {center : ℂ}
    (boundaryControl : ∀ patch, BoundaryCloseToCircle scales motion time index patch boundaryError)
    (radiusPositive : 0 < scales.radius (index.val + 1))
    (positiveBound : ‖positiveHalfDiagonal motion time index‖ ≤ diagonalBound)
    (negativeBound : ‖negativeHalfDiagonal motion time index‖ ≤ diagonalBound)
    (asymmetryControl : ‖centroidAsymmetry motion time index‖ ≤ asymmetryBound)
    (centerControl : ‖quadrupoleCenter motion time index - center‖ ≤ centerError)
    (patch : Fin 4) (position : ℂ) (member : position ∈ motion.domain time index patch) :
    ‖position - center‖ ≤ scales.radius (index.val + 1) * (1 + boundaryError) +
      asymmetryBound + diagonalBound + centerError := by
  have domainBound := evolution.domain_subset_centroid_ball inside index patch (boundaryControl patch) radiusPositive member
  rw [Metric.mem_closedBall, dist_eq_norm] at domainBound
  have centroidBound := patchCentroid_distance_le_of_halfDiagonals positiveBound negativeBound asymmetryControl patch
  have decomposition : position - center =
      (position - patchCentroid motion time index patch) +
        (patchCentroid motion time index patch - quadrupoleCenter motion time index) +
        (quadrupoleCenter motion time index - center) := by ring
  rw [decomposition]
  have estimate := (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add domainBound centroidBound)) centerControl)
  linarith

end EulerNonuniqueness.Paper
