import EulerNonuniqueness.Section4.PaperHalfDiagonalDynamics
import EulerNonuniqueness.Section4.PaperCoarseUpperBranch
import EulerNonuniqueness.Section6.ReferenceChartAnnulus

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def diagonalOddForcingRate {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℝ :=
  let positions := fun patch => patchCentroid motion time index patch
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let forcing := fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)
  2 * @inner ℝ ℂ _ (positiveHalfDiagonal motion time index) forcing.1 -
    2 * @inner ℝ ℂ _ (negativeHalfDiagonal motion time index) forcing.2

theorem FinitePatchEvolution.diagonalDifference_hasDerivAt_of_small_shape
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radii : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count) (inside : time ∈ Ioo 0 horizon)
    (small : |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4) :
    HasDerivAt (fun current => diagonalDifference motion current index)
      (diagonalOddForcingRate scales motion index time) time := by
  have upper := paper_shape_ratio_im_pos_of_small motion time index small
  have identity := pointShapeChart_eq_paper_shape_of_upper motion time index upper
  have chartSmall : |(pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
      |(pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4 := by
    simpa only [identity] using small
  obtain ⟨positiveNonzero, negativeNonzero, _, ratioUpper⟩ :=
    pointShapeChart_reference_annulus (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) chartSmall
  have positiveNorm : 0 < ‖positiveHalfDiagonal motion time index‖ := norm_pos_iff.mpr positiveNonzero
  have normOrder : ‖negativeHalfDiagonal motion time index‖ < ‖positiveHalfDiagonal motion time index‖ := by
    have scaled := (div_le_iff₀ positiveNorm).mp ratioUpper
    linarith
  have differenceNonzero : positiveHalfDiagonal motion time index - negativeHalfDiagonal motion time index ≠ 0 := by
    intro zero
    rw [sub_eq_zero.mp zero] at normOrder
    exact lt_irrefl _ normOrder
  have sumNonzero : positiveHalfDiagonal motion time index + negativeHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have equality : negativeHalfDiagonal motion time index = -positiveHalfDiagonal motion time index :=
      eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using zero)
    rw [equality, norm_neg] at normOrder
    exact lt_irrefl _ normOrder
  exact evolution.centroid_diagonalDifference_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive
    ratioPositive radii control separated index inside
    (centrallySymmetricFourPoint_noncollision positiveNonzero negativeNonzero differenceNonzero sumNonzero) normOrder

end EulerNonuniqueness.Paper
