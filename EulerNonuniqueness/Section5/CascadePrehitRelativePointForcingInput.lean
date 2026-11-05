import EulerNonuniqueness.Section6.PaperShapeForcingRawBound
import EulerNonuniqueness.Section5.CascadePrehitRelativeRawForcingInput
import EulerNonuniqueness.Section5.CascadePrehitTotalOddForcingSmall
import EulerNonuniqueness.Section5.CascadePrehitShapeForcingOperator
import EulerNonuniqueness.General.RelativeLinearForcingBudget

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_prehit_relative_point_forcing_input (scales : Scales)
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
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let length := changed.length (index.val + 1)
      let radius := factor / 39321600 * changed.location (index.val + 1)
      let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
      ‖referencePointShapeForcing changed first time index - referencePointShapeForcing changed second time index‖ ≤
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + positions) +
        30 * (‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / length) +
        90 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
          quadrupoleExteriorCoefficient changed second index time radius power‖) := by
  filter_upwards [scales.eventually_cascade_prehit_relative_raw_forcing_input amplitudePositive ratioBound alphaPositive orbit sectionTime
      rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall (show 0 < tolerance / 60 by positivity),
    scales.eventually_cascade_prehit_total_odd_forcing_small amplitudePositive ratioBound alphaPositive orbit sectionTime
      rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall (show 0 < tolerance / (2 * 32844) by positivity),
    scales.eventually_cascade_prehit_shape_forcing_operator amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (le_trans (by norm_num) boundaryOne) thresholdSmall referenceNonnegative] with frequency differences totals operators
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
    (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
  have lengthPositive : 0 < length := changed.length_pos _
  have differenceBound := differences count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have totalBound := totals count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have operatorBounds := operators prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only at differenceBound totalBound operatorBounds
  have positionsIdentity : ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
      (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ = length * positions := by
    dsimp only [positions]
    field_simp
  rw [positionsIdentity] at operatorBounds
  have actual := referencePointShapeForcing_relative_raw_bound changed first second time index
  dsimp only at actual
  exact EulerNonuniqueness.General.relative_linear_forcing_normalized_budget lengthPositive tolerancePositive
    (norm_nonneg (relativeNormalizedFirstMoment changed first second index time))
    (show 0 ≤ positions from div_nonneg (norm_nonneg _) lengthPositive.le)
    (div_nonneg (norm_nonneg _) lengthPositive.le) (tsum_nonneg fun _ => norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) actual operatorBounds.1 differenceBound operatorBounds.2 totalBound

end EulerNonuniqueness.Paper
