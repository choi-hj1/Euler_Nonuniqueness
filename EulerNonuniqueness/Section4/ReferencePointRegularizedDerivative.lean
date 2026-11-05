import EulerNonuniqueness.Section4.ReferencePaperShapeRegularity
import EulerNonuniqueness.Section6.ReferenceChartImaginaryGap

noncomputable section

open Set Filter EulerNonuniqueness.Section6
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centroid_regularized_shape_hasDerivAt_of_point_safety {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index)
    (upper : 0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im)
    (small : |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4) :
    HasDerivAt (fun current => regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
      (positiveHalfDiagonal family.patchMotion current index) (negativeHalfDiagonal family.patchMotion current index))
      (referencePointShapeVelocity scales family.patchMotion time index) time := by
  have chartIdentity := pointShapeChart_eq_paper_shape_of_upper family.patchMotion time index upper
  have coherentSmall : |(pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
      (negativeHalfDiagonal family.patchMotion time index)).1| +
      |(pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
      (negativeHalfDiagonal family.patchMotion time index)).2| ≤ 1 / 4 := by
    simpa only [chartIdentity] using small
  obtain ⟨positiveNonzero, negativeNonzero, _, _⟩ := pointShapeChart_reference_annulus _ _ coherentSmall
  have denominatorStrict : scales.length (index.val + 1) ^ 2 / 2 <
      ‖positiveHalfDiagonal family.patchMotion time index‖ ^ 2 := by
    dsimp only [diagonalDifference] at differenceLower
    nlinarith [sq_pos_of_pos (norm_pos_iff.mpr negativeNonzero)]
  have imaginaryGap := pointShapeChart_reference_imaginary_gap _ _ coherentSmall upper
  have imaginaryStrict : (1 / 16 : ℝ) < (negativeHalfDiagonal family.patchMotion time index /
      positiveHalfDiagonal family.patchMotion time index).im := by linarith
  obtain ⟨positiveSmooth, negativeSmooth⟩ := family.halfDiagonals_contDiffAt index pathInside
  have denominatorContinuous := positiveSmooth.continuousAt.norm.pow 2
  have imaginaryContinuous := Complex.continuous_im.continuousAt.comp
    (negativeSmooth.continuousAt.div positiveSmooth.continuousAt positiveNonzero)
  have agreement : (fun current => regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
      (positiveHalfDiagonal family.patchMotion current index) (negativeHalfDiagonal family.patchMotion current index)) =ᶠ[𝓝 time]
      (fun current => (unstableShape family.patchMotion current index, stableShape family.patchMotion current index)) := by
    filter_upwards [denominatorContinuous.eventually (Ioi_mem_nhds denominatorStrict),
      imaginaryContinuous.eventually (Ioi_mem_nhds imaginaryStrict)] with current denominator imaginary
    exact regularizedShapeCoordinates_eq_paper family.patchMotion current index denominator.le imaginary.le
  exact (family.centroid_paper_shape_hasDerivAt_of_upper evolution inside index pathInside material upper small).congr_of_eventuallyEq agreement

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
