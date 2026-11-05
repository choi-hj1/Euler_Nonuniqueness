import EulerNonuniqueness.Section4.RegularizedShapeBranch
import EulerNonuniqueness.Section4.ReferenceInitialShapeCoordinates
import EulerNonuniqueness.Section4.ReferencePaperShapeRegularity
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

theorem reference_paper_shape_of_regularized_box {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon threshold radius : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonNonnegative : 0 ≤ horizon) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {phase unstable : Fin count → ℝ}
    (initial : ReferenceInitialDisks scales family.patchMotion phase unstable threshold) (thresholdSmall : threshold ≤ 1 / 2)
    (radiusSmall : radius ≤ 1 / 8)
    (inside : ∀ time ∈ Icc 0 horizon, ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (differenceLower : ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index)
    (unstableBound : ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)).1| ≤ radius)
    (stableBound : ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)).2| ≤ radius) :
    ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
      0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im ∧
      regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index) =
          (unstableShape family.patchMotion time index, stableShape family.patchMotion time index) ∧
      |unstableShape family.patchMotion time index| ≤ radius ∧ |stableShape family.patchMotion time index| ≤ radius ∧
      |radialShape family.patchMotion time index| ≤ 2 * radius := by
  have denominatorLower (time : ℝ) (member : time ∈ Icc 0 horizon) (index : Fin count) :
      scales.length (index.val + 1) ^ 2 / 2 ≤ ‖positiveHalfDiagonal family.patchMotion time index‖ ^ 2 := by
    have lower := differenceLower time member index
    dsimp only [diagonalDifference] at lower
    nlinarith [sq_nonneg ‖negativeHalfDiagonal family.patchMotion time index‖]
  have positiveNonzero (time : ℝ) (member : time ∈ Icc 0 horizon) (index : Fin count) :
      positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
    intro zero
    have lower := denominatorLower time member index
    rw [zero, norm_zero] at lower
    nlinarith [sq_pos_of_pos (scales.length_pos (index.val + 1))]
  have chartSmall (time : ℝ) (member : time ∈ Icc 0 horizon) (index : Fin count) :
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)).1| +
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)).2| ≤ 1 / 4 := by
    linarith [unstableBound time member index, stableBound time member index]
  have upper (index : Fin count) : ∀ time ∈ Icc 0 horizon,
      0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im := by
    have positiveContinuous : ContinuousOn (fun time => positiveHalfDiagonal family.patchMotion time index) (Icc 0 horizon) := by
      intro time member
      exact (family.halfDiagonals_contDiffAt index (fun patch => inside time member _)).1.continuousAt.continuousWithinAt
    have negativeContinuous : ContinuousOn (fun time => negativeHalfDiagonal family.patchMotion time index) (Icc 0 horizon) := by
      intro time member
      exact (family.halfDiagonals_contDiffAt index (fun patch => inside time member _)).2.continuousAt.continuousWithinAt
    exact upperHalfPlane_of_initial_and_square_left (negativeContinuous.div positiveContinuous (fun time member => positiveNonzero time member index))
      (evolution.reference_initial_paper_shape horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial thresholdSmall index).1
      (fun time member => regularizedShapeCoordinates_square_left (denominatorLower time member index) (chartSmall time member index))
  intro time member index
  have agreement := regularizedShapeCoordinates_eq_paper_of_small_upper family.patchMotion time index
    (denominatorLower time member index) (chartSmall time member index) (upper index time member)
  have actualUnstable : |unstableShape family.patchMotion time index| ≤ radius := by
    simpa only [agreement] using unstableBound time member index
  have actualStable : |stableShape family.patchMotion time index| ≤ radius := by
    simpa only [agreement] using stableBound time member index
  refine ⟨upper index time member, agreement, actualUnstable, actualStable, ?_⟩
  have radialIdentity : radialShape family.patchMotion time index = unstableShape family.patchMotion time index +
      stableShape family.patchMotion time index := by dsimp only [unstableShape, stableShape]; ring
  rw [radialIdentity]
  exact (abs_add _ _).trans (by linarith)

theorem reference_centroid_field_geometry_of_regularized_box {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon threshold radius : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonNonnegative : 0 ≤ horizon) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {phase unstable : Fin count → ℝ}
    (initial : ReferenceInitialDisks scales family.patchMotion phase unstable threshold) (thresholdSmall : threshold ≤ 1 / 2)
    (radiusSmall : radius ≤ 1 / 8)
    (inside : ∀ time ∈ Icc 0 horizon, ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (differenceLower : ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index)
    (differenceUpper : ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
      diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (unstableBound : ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)).1| ≤ radius)
    (stableBound : ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)).2| ≤ radius)
    (asymmetrySmall : ∀ time ∈ Icc 0 horizon, ∀ index, ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ time ∈ Icc 0 horizon, ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusLengthSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (deformation : ℝ → Fin count → ℝ)
    (control : ∀ time ∈ Icc 0 horizon, ∀ index patch, BoundaryCloseToCircle scales family.patchMotion time index patch (deformation time index))
    (nonnegative : ∀ time ∈ Icc 0 horizon, ∀ index, 0 ≤ deformation time index)
    (small : ∀ time ∈ Icc 0 horizon, ∀ index, deformation time index ≤ 1 / 16) :
    ∀ time ∈ Icc 0 horizon, ∀ index, ReferenceCentroidFieldGeometry scales family.patchMotion time index := by
  have shape := family.reference_paper_shape_of_regularized_box evolution horizonNonnegative amplitudePositive frequencyPositive ratioPositive
    initial thresholdSmall radiusSmall inside differenceLower unstableBound stableBound
  intro time member index
  apply evolution.reference_centroid_field_geometry member amplitudePositive frequencyPositive ratioPositive
    (differenceLower time member) (differenceUpper time member) _ (asymmetrySmall time member) (centerSeparation time member)
    lengthSmall radiusLengthSmall (deformation time) (control time member) (nonnegative time member) (small time member) index
  intro source
  exact ((shape time member source).2.2.2.2).trans (by linarith)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
