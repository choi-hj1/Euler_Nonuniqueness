import EulerNonuniqueness.Section5.CascadePrehitOddInternalSmall
import EulerNonuniqueness.Section5.CascadePrehitTotalOddForcingSmall
import EulerNonuniqueness.Section5.CascadePrehitShapeForcingOperator
import EulerNonuniqueness.Section5.CascadePrehitExteriorTaylorReturn
import EulerNonuniqueness.Section6.PaperActualRelativeStrainForcing
import EulerNonuniqueness.Section6.PaperStrainForcingVectorIdentity
import EulerNonuniqueness.General.RelativeShapeForcingBudget

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem Scales.eventually_cascade_prehit_relative_shape_forcing_input (scales : Scales)
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
      ‖referencePointShapeForcing changed first time index - referencePointShapeForcing changed second time index -
          quadrupoleRelativeLeadingStrain changed first second time index‖ ≤
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + positions) +
        30 * (‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / length) +
        30 * ((length / radius) * (6 * (96 / Real.pi * (2304 * changed.strain)) * positions +
          9 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius (power + 1) -
            quadrupoleExteriorCoefficient changed second index time radius (power + 1)‖))) := by
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := le_trans (by norm_num) boundaryOne
  have strainLimit : Tendsto (fun frequency : ℝ =>
      30 * (96 / Real.pi * (2304 * ({scales with frequency := frequency} : Scales).strain))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 2304).const_mul
      (96 / Real.pi)).const_mul 30
  filter_upwards [scales.eventually_cascade_prehit_odd_internal_small amplitudePositive ratioBound alphaPositive rootPositive
      boundaryNonnegative thresholdSmall referenceNonnegative (show 0 < tolerance / 90 by positivity),
    scales.eventually_cascade_prehit_total_odd_forcing_small amplitudePositive ratioBound alphaPositive orbit sectionTime
      rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall
      (show 0 < tolerance / (3 * 32844) by positivity),
    scales.eventually_cascade_prehit_shape_forcing_operator amplitudePositive ratioBound alphaPositive rootPositive
      boundaryNonnegative thresholdSmall referenceNonnegative,
    scales.eventually_cascade_prehit_exterior_taylor_return amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_head_tail amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    strainLimit.eventually (eventually_lt_nhds (show 0 < tolerance / 3 by positivity))]
    with frequency internal total operators taylor coefficients strainSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let budget := 96 / Real.pi * (2304 * changed.strain)
  let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
    (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
  let pointFirst := (positiveHalfDiagonal first time index, negativeHalfDiagonal first time index)
  let pointSecond := (positiveHalfDiagonal second time index, negativeHalfDiagonal second time index)
  have lengthPositive : 0 < length := changed.length_pos _
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have internalBound := internal prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have totalBound := total count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have operatorBounds := operators prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have taylorBound := taylor count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only at internalBound totalBound operatorBounds taylorBound
  rw [quadrupoleNormalizedCentroidOffsets_relative_norm_eq_div first second index time lengthPositive] at taylorBound
  have head := (coefficients count phase dipoleAngle prepared path time fullInside index 0).2.1
  change ‖quadrupoleExteriorCoefficient changed first index time radius 0‖ ≤ budget at head
  have budgetNonnegative : 0 ≤ budget := (norm_nonneg _).trans head
  have strainBound : ‖quadrupoleExternalShapeStrain changed first time index‖ ≤ budget := by
    simpa only [quadrupoleExteriorCoefficient, exteriorVorticityCoefficient_zero_eq_complexStrain,
      quadrupoleExternalShapeStrain] using head
  let difference := (fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
    (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)
  have oddIdentity : fourPointOddPart difference = pointFirst - pointSecond := by
    ext <;> simp only [fourPointOddPart, difference, pointFirst, pointSecond, Pi.sub_apply,
      Prod.fst_sub, Prod.snd_sub, positiveHalfDiagonal, negativeHalfDiagonal] <;> ring
  have diagonalBound := fourPointOddPart_norm_le difference
  rw [oddIdentity] at diagonalBound
  have positionsIdentity : ‖difference‖ = length * positions := by
    dsimp only [positions, difference]
    field_simp
  rw [positionsIdentity] at diagonalBound
  have variationBound := operatorBounds.2
  change pointShapeForcingOperatorVariation pointFirst pointSecond ≤ 32844 / length ^ 2 * ‖difference‖ at variationBound
  rw [positionsIdentity] at variationBound
  have actual := referencePointShapeForcing_relative_actual_strain_bound changed first second time index
  rw [← quadrupoleTotalOddForcing_eq_strain_remainder changed first time index] at actual
  exact EulerNonuniqueness.General.relative_shape_forcing_normalized_budget lengthPositive tolerancePositive
    (norm_nonneg (relativeNormalizedFirstMoment changed first second index time))
    (show 0 ≤ positions from div_nonneg (norm_nonneg _) lengthPositive.le)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    budgetNonnegative actual operatorBounds.1 internalBound taylorBound strainBound diagonalBound variationBound totalBound strainSmall.le

end EulerNonuniqueness.Paper
