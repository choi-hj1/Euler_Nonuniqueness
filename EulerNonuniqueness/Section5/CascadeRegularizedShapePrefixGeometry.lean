import EulerNonuniqueness.Section5.CascadeNonterminalInitialMoments
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation
import EulerNonuniqueness.Section4.RegularizedShapeBranch
import EulerNonuniqueness.Section4.PaperCoarseUpperBranch

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

theorem regularized_shape_prefix_eq_paper {count : ℕ} (motion : PatchMotion count)
    (index : Fin count) {horizon denominatorFloor : ℝ} (floorPositive : 0 < denominatorFloor)
    (positiveContinuous : ContinuousOn (fun time => positiveHalfDiagonal motion time index) (Icc 0 horizon))
    (negativeContinuous : ContinuousOn (fun time => negativeHalfDiagonal motion time index) (Icc 0 horizon))
    (denominatorLower : ∀ time ∈ Icc 0 horizon, denominatorFloor ≤ ‖positiveHalfDiagonal motion time index‖ ^ 2)
    (initialUpper : 0 < (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im)
    (small : ∀ time ∈ Icc 0 horizon,
      |(regularizedShapeCoordinates denominatorFloor (1 / 16)
        (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
      |(regularizedShapeCoordinates denominatorFloor (1 / 16)
        (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4) :
    ∀ time ∈ Icc 0 horizon, regularizedShapeCoordinates denominatorFloor (1 / 16)
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
        (unstableShape motion time index, stableShape motion time index) := by
  have nonzero (time : ℝ) (inside : time ∈ Icc 0 horizon) : positiveHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have lower := denominatorLower time inside
    rw [zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at lower
    linarith only [lower, floorPositive]
  have quotientContinuous := negativeContinuous.div positiveContinuous nonzero
  have left (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      ((negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index) ^ 2).re < 0 :=
    regularizedShapeCoordinates_square_left (denominatorLower time inside) (small time inside)
  have upper := Section6.upperHalfPlane_of_initial_and_square_left quotientContinuous initialUpper left
  intro time inside
  exact regularizedShapeCoordinates_eq_paper_of_small_upper motion time index
    (denominatorLower time inside) (small time inside) (upper time inside)

theorem actual_initial_regularized_geometry
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (index : Fin count) (nonterminal : index.val + 1 < count)
    {radius : ℝ} (radiusPositive : 0 < radius) (radiusQuarter : radius ≤ 1 / 4)
    (denominatorLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      ‖positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion 0 index‖ ^ 2)
    (referenceSmall : |unstableShape prepared.reference 0 index| + |stableShape prepared.reference 0 index| < radius / 8) :
    let motion := prepared.trajectory.movingFamily.patchMotion
    let regularized := fun time => regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
    Continuous (fun time => positiveHalfDiagonal motion time index) ∧
    Continuous (fun time => negativeHalfDiagonal motion time index) ∧ Continuous regularized ∧
    0 < (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im ∧
    |(regularized 0).1| + |(regularized 0).2| < radius := by
  dsimp only
  let motion := prepared.trajectory.movingFamily.patchMotion
  let regularized := fun time => regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
    (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
  have positiveContinuous : Continuous (fun time : ℝ => positiveHalfDiagonal motion time index) := by
    exact ((prepared.trajectory.movingFamily.patchCentroid_continuous index 0).sub
      (prepared.trajectory.movingFamily.patchCentroid_continuous index 1)).div_const 2
  have negativeContinuous : Continuous (fun time : ℝ => negativeHalfDiagonal motion time index) := by
    exact ((prepared.trajectory.movingFamily.patchCentroid_continuous index 2).sub
      (prepared.trajectory.movingFamily.patchCentroid_continuous index 3)).div_const 2
  have diagonalContinuous : Continuous (fun time : ℝ =>
      (positiveHalfDiagonal motion time index, negativeHalfDiagonal motion time index)) :=
    positiveContinuous.prodMk negativeContinuous
  have shapeContinuous : Continuous (fun point : ℂ × ℂ =>
      regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16) point.1 point.2) :=
    regularizedShapeCoordinates_continuous
      (div_pos (sq_pos_of_pos (scales.length_pos _)) (by norm_num)) (by norm_num)
  have composed := shapeContinuous.comp diagonalContinuous
  have regularizedContinuous : Continuous regularized := by
    simpa only [regularized, Function.comp_def] using composed
  have positive : positiveHalfDiagonal motion 0 index = positiveHalfDiagonal prepared.reference 0 index := by
    simp only [motion, positiveHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
  have negative : negativeHalfDiagonal motion 0 index = negativeHalfDiagonal prepared.reference 0 index := by
    simp only [motion, negativeHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
  have first : unstableShape motion 0 index = unstableShape prepared.reference 0 index := by
    simp only [unstableShape, radialShape, angularShape, positive, negative]
  have second : stableShape motion 0 index = stableShape prepared.reference 0 index := by
    simp only [stableShape, radialShape, angularShape, positive, negative]
  have actualSmall : |unstableShape motion 0 index| + |stableShape motion 0 index| < radius / 8 := by
    rw [first, second]
    exact referenceSmall
  have actualQuarter : |unstableShape motion 0 index| + |stableShape motion 0 index| ≤ 1 / 4 := by
    linarith only [actualSmall, radiusPositive, radiusQuarter]
  have upper := paper_shape_ratio_im_pos_of_small motion 0 index actualQuarter
  have chartSmall : |(Section6.pointShapeChart (positiveHalfDiagonal motion 0 index) (negativeHalfDiagonal motion 0 index)).1| +
      |(Section6.pointShapeChart (positiveHalfDiagonal motion 0 index) (negativeHalfDiagonal motion 0 index)).2| ≤ 1 / 4 := by
    rw [pointShapeChart_eq_paper_shape_of_upper motion 0 index upper]
    exact actualQuarter
  have gap := Section6.pointShapeChart_reference_imaginary_gap _ _ chartSmall upper
  have agreement : regularized 0 = (unstableShape motion 0 index, stableShape motion 0 index) :=
    regularizedShapeCoordinates_eq_paper motion 0 index denominatorLower
      ((by norm_num : (1 / 16 : ℝ) ≤ 1 / 8).trans gap)
  refine ⟨positiveContinuous, negativeContinuous, regularizedContinuous, upper, ?_⟩
  change |(regularized 0).1| + |(regularized 0).2| < radius
  rw [agreement]
  linarith only [actualSmall, radiusPositive]

end EulerNonuniqueness.Paper
