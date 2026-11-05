import EulerNonuniqueness.Section6.AnnularShapeForcingOperator
import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation
import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData
import EulerNonuniqueness.Section4.ReferenceForcingWeight
import EulerNonuniqueness.Section6.PaperShapeBranch

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6 EulerNonuniqueness.Section2

private theorem half_diagonal_annular_data {count : ℕ} (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    {length : ℝ} (lengthPositive : 0 < length)
    (lower : length ^ 2 / 2 ≤ diagonalDifference motion time index)
    (upper : diagonalDifference motion time index ≤ 2 * length ^ 2)
    (radial : |radialShape motion time index| ≤ 1 / 2) :
    length / 2 ≤ ‖positiveHalfDiagonal motion time index‖ ∧
    length / 8 ≤ ‖negativeHalfDiagonal motion time index‖ ∧
    ‖positiveHalfDiagonal motion time index‖ ≤ 2 * length ∧
    ‖negativeHalfDiagonal motion time index‖ ≤ 2 * length ∧
    pointShapeRatio (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) / rhombusRatio + 1 ≤ 3 := by
  have lowerData := halfDiagonals_lower_and_ratio_of_reference_shape motion time index lengthPositive lower radial
  have upperData := halfDiagonals_norm_le_of_reference_shape lengthPositive
    ((by positivity : 0 < length ^ 2 / 2).trans_le lower) upper ((le_abs_self _).trans radial)
  refine ⟨lowerData.1, lowerData.2.1, upperData.1, upperData.2, ?_⟩
  have radialUpper := (le_abs_self (radialShape motion time index)).trans radial
  have identity : pointShapeRatio (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) /
      rhombusRatio + 1 = radialShape motion time index + 2 := by
    unfold pointShapeRatio radialShape
    rw [sub_div, div_self reference_rhombusRatio_bounds.1.ne']
    ring
  rw [identity]
  linarith

theorem Scales.eventually_cascade_prehit_shape_forcing_operator (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {scaleRoot boundaryConstant threshold referenceConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius factor monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, factor ≤ 1 / 8 →
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      pointShapeForcingWeight (positiveHalfDiagonal second time index, negativeHalfDiagonal second time index) ≤
          30 / changed.length (index.val + 1) ∧
      pointShapeForcingOperatorVariation
          (positiveHalfDiagonal first time index, negativeHalfDiagonal first time index)
          (positiveHalfDiagonal second time index, negativeHalfDiagonal second time index) ≤
        32844 / changed.length (index.val + 1) ^ 2 *
          ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
            (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ := by
  filter_upwards [scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative]
    with frequency joint mechanical
  intro orbit sectionTime phase dipoleAngle shapeRadius factor monitor count prepared path factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  have lengthPositive : 0 < length := changed.length_pos _
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
  have referenceData := mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
    prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside index
  have refLower : length ^ 2 / 2 ≤ diagonalDifference second time index := by
    simpa only [second, prepared.referenceIdentity] using referenceData.2.1
  have refUpper : diagonalDifference second time index ≤ 2 * length ^ 2 := by
    simpa only [second, prepared.referenceIdentity] using referenceData.2.2.1
  have refSmall : |unstableShape second time index| + |stableShape second time index| ≤ 1 / 4 := by
    have q : |unstableShape second time index| ≤ threshold := by
      simpa only [second, prepared.referenceIdentity] using referenceData.2.2.2.2.1
    have p : |stableShape second time index| ≤ threshold := by
      simpa only [second, prepared.referenceIdentity] using referenceData.2.2.2.2.2.1
    linarith
  have refRadial : |radialShape second time index| ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans (refSmall.trans (by norm_num))
  have jointData := (joint prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall time inside).1
  have altLower : length ^ 2 / 2 ≤ diagonalDifference first time index := by
    have ratioLower := neg_abs_le (diagonalDifference first time index / length ^ 2 - 1)
    have bound : (3 / 4 : ℝ) ≤ diagonalDifference first time index / length ^ 2 := by linarith
    nlinarith [(le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp bound]
  have altUpper : diagonalDifference first time index ≤ 2 * length ^ 2 := by
    have ratioUpper := le_abs_self (diagonalDifference first time index / length ^ 2 - 1)
    have bound : diagonalDifference first time index / length ^ 2 ≤ (5 / 4 : ℝ) := by linarith
    nlinarith [(div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp bound]
  have firstData := half_diagonal_annular_data first time index lengthPositive altLower altUpper (radialSmall time inside)
  have secondData := half_diagonal_annular_data second time index lengthPositive refLower refUpper refRadial
  constructor
  · have upper : 0 < (negativeHalfDiagonal second time index / positiveHalfDiagonal second time index).im := by
      simpa only [second, prepared.referenceIdentity] using referenceData.2.2.2.2.2.2.1
    have chartSmall : |(pointShapeChart (positiveHalfDiagonal second time index) (negativeHalfDiagonal second time index)).1| +
        |(pointShapeChart (positiveHalfDiagonal second time index) (negativeHalfDiagonal second time index)).2| ≤ 1 / 4 := by
      rw [pointShapeChart_eq_paper_shape_of_upper second time index upper]
      exact refSmall
    exact pointShapeForcingWeight_reference_le lengthPositive refLower chartSmall
  · have actual := pointShapeForcingOperatorVariation_annular_bound
      (positiveHalfDiagonal first time index, negativeHalfDiagonal first time index)
      (positiveHalfDiagonal second time index, negativeHalfDiagonal second time index) lengthPositive
      firstData.1 secondData.1 firstData.2.1 secondData.2.1 firstData.2.2.1 secondData.2.2.1
      firstData.2.2.2.1 secondData.2.2.2.1 firstData.2.2.2.2
    let difference := (fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
      (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)
    have oddIdentity : fourPointOddPart difference =
        (positiveHalfDiagonal first time index, negativeHalfDiagonal first time index) -
          (positiveHalfDiagonal second time index, negativeHalfDiagonal second time index) := by
      ext <;> simp only [fourPointOddPart, difference, Pi.sub_apply, Prod.fst_sub, Prod.snd_sub,
        positiveHalfDiagonal, negativeHalfDiagonal] <;> ring
    have oddBound := fourPointOddPart_norm_le difference
    rw [oddIdentity] at oddBound
    exact actual.trans (mul_le_mul_of_nonneg_left oddBound (by positivity))

end EulerNonuniqueness.Paper
