import EulerNonuniqueness.Section6.PaperStrongNeutralReconstruction
import EulerNonuniqueness.Section6.SourcePacketReceiverDiagonalSmallness
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_cascade_strong_neutral_reconstruction
    {graph coordinate correction : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (correctionSmooth : ContDiffAt ℝ 1 correction 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {scaleRoot boundaryConstant threshold referenceConstant : ℝ},
      0 < scaleRoot → 0 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius factor monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, factor ≤ 1 / 8 →
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius →
      ∀ firstPhase secondPhase : ℝ → ℝ,
      positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index =
        (‖positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index‖ : ℂ) * Complex.exp (Complex.I * (firstPhase time : ℂ)) →
      positiveHalfDiagonal prepared.reference time index =
        (‖positiveHalfDiagonal prepared.reference time index‖ : ℂ) * Complex.exp (Complex.I * (secondPhase time : ℂ)) →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / changed.length (index.val + 1) ≤
        (changed.length (index.val + 1) / (4 * changed.location (index.val + 1))) *
          ‖relativeNormalizedFirstMoment changed first second index time‖ +
        constant * (|diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2 +
          |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
          |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2| +
          |correctedPaperPhase correction firstPhase first index time - correctedPaperPhase correction secondPhase second index time|) := by
  obtain ⟨baseRadius, basePositive, constant, constantOne, reconstruction⟩ :=
    sameGraph_exists_uniform_strong_neutral_reconstruction graphSmooth coordinateSmooth correctionSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  let radius := min (baseRadius / 4) (1 / 4)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusQuarter : radius ≤ 1 / 4 := min_le_right _ _
  have radiusBase : radius ≤ baseRadius / 4 := min_le_left _ _
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant threshold referenceConstant
    rootPositive boundaryNonnegative thresholdSmall referenceNonnegative
  filter_upwards [scales.eventually_actual_receiver_diagonal_small amplitudePositive ratioBound alphaPositive rootPositive
      boundaryNonnegative radiusPositive,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative radiusPositive]
    with frequency alternative reference
  intro orbit sectionTime phase dipoleAngle shapeRadius factor monitor count prepared path factorSmall index nonterminal finish
    finishNonnegative finishBound radialSmall time inside currentSmall firstPhase secondPhase firstPolar secondPolar
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  have lengthPositive : 0 < length := changed.length_pos _
  have alternativeDefect := alternative prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  change |diagonalDifference first time index / length ^ 2 - 1| ≤ radius at alternativeDefect
  have referenceInside : time ∈ Icc (0 : ℝ) 1 := ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩
  have referenceDefect := reference prepared time referenceInside index
  have firstPositive : 0 < diagonalDifference first time index := by
    have negative := neg_abs_le (diagonalDifference first time index / length ^ 2 - 1)
    have ratioPositive : 0 < diagonalDifference first time index / length ^ 2 := by linarith
    exact (div_pos_iff.mp ratioPositive).resolve_right (by
      intro negative
      exact (sq_pos_of_pos lengthPositive).not_le negative.2.le) |>.1
  have secondPositive : 0 < diagonalDifference second time index := by
    have defectBound : |diagonalDifference second time index / length ^ 2 - 1| < radius := by
      have firstNonnegative := abs_nonneg (unstableShape second time index)
      have secondNonnegative := abs_nonneg (stableShape second time index)
      change |diagonalDifference second time index / length ^ 2 - 1| +
        |unstableShape second time index| + |stableShape second time index| < radius at referenceDefect
      linarith
    have negative := neg_abs_le (diagonalDifference second time index / length ^ 2 - 1)
    have ratioPositive : 0 < diagonalDifference second time index / length ^ 2 := by linarith
    exact (div_pos_iff.mp ratioPositive).resolve_right (by
      intro negative
      exact (sq_pos_of_pos lengthPositive).not_le negative.2.le) |>.1
  have firstSmall : |diagonalDifference first time index / length ^ 2 - 1| +
      |unstableShape first time index| + |stableShape first time index| < baseRadius := by
    change |unstableShape first time index| + |stableShape first time index| ≤ radius at currentSmall
    linarith
  have secondSmall : |diagonalDifference second time index / length ^ 2 - 1| +
      |unstableShape second time index| + |stableShape second time index| < baseRadius := by
    change |diagonalDifference second time index / length ^ 2 - 1| +
      |unstableShape second time index| + |stableShape second time index| < radius at referenceDefect
    linarith
  exact reconstruction changed first second index time firstPhase secondPhase firstPositive secondPositive
    firstPolar secondPolar firstSmall secondSmall

end EulerNonuniqueness.Paper
