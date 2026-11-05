import EulerNonuniqueness.Section5.CascadePrehitTotalOddForcingSmall
import EulerNonuniqueness.Section5.CascadePrehitShapeForcingOperator

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_cascade_prehit_point_forcing_small (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {scaleRoot boundaryConstant threshold referenceConstant factor tolerance : ℝ}
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
      ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 4 →
      ‖referencePointShapeForcing {scales with frequency := frequency}
        prepared.trajectory.movingFamily.patchMotion time index‖ ≤ tolerance := by
  filter_upwards [scales.eventually_cascade_prehit_total_odd_forcing_small amplitudePositive ratioBound alphaPositive
      orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall
      (show 0 < tolerance / 30 by positivity),
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (le_trans (by norm_num) boundaryOne)]
    with frequency total joint
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound
    radial time inside small
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let length := changed.length (index.val + 1)
  let forcing := fourPointTotalOddForcing (changed.omega (index.val + 1) * length ^ 2)
    (fun patch => patchCentroid motion time index patch) (quadrupoleCentroidForcing changed motion time index)
  have lengthPositive : 0 < length := changed.length_pos _
  have diagonal := (joint prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal
    finish finishNonnegative finishBound radial time inside).1
  have lower : length ^ 2 / 2 ≤ diagonalDifference motion time index := by
    have negative := neg_abs_le (diagonalDifference motion time index / length ^ 2 - 1)
    have ratioLower : (3 / 4 : ℝ) ≤ diagonalDifference motion time index / length ^ 2 := by
      change |diagonalDifference motion time index / length ^ 2 - 1| ≤ 1 / 4 at diagonal
      linarith
    nlinarith [(le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp ratioLower]
  have chartSmall : |(pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
      |(pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4 := by
    rw [pointShapeChart_eq_paper_shape_of_upper motion time index (paper_shape_ratio_im_pos_of_small motion time index small)]
    exact small
  have weight := pointShapeForcingWeight_reference_le lengthPositive lower chartSmall
  have actual := pointShapeForcing_norm_bound (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
    forcing.1 forcing.2
  change ‖referencePointShapeForcing changed motion time index‖ ≤
    pointShapeForcingWeight (positiveHalfDiagonal motion time index, negativeHalfDiagonal motion time index) * ‖forcing‖ at actual
  have raw := total count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radial time inside
  change ‖forcing‖ / length ≤ tolerance / 30 at raw
  have bounded := actual.trans (mul_le_mul_of_nonneg_right weight (norm_nonneg forcing))
  have identity : (30 / length) * ‖forcing‖ = 30 * (‖forcing‖ / length) := by ring
  rw [identity] at bounded
  exact bounded.trans ((mul_le_mul_of_nonneg_left raw (by norm_num : (0 : ℝ) ≤ 30)).trans_eq (by ring))

end EulerNonuniqueness.Paper
