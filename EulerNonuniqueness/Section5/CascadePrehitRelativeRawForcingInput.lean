import EulerNonuniqueness.Section6.PaperOddForcingRelativeSplit
import EulerNonuniqueness.Section5.CascadePrehitOddInternalSmall
import EulerNonuniqueness.Section5.CascadePrehitCenteredExteriorReturn
import EulerNonuniqueness.Section5.CascadePrehitExternalDilationReturn

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_cascade_prehit_relative_raw_forcing_input (scales : Scales)
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
      ‖fourPointTotalOddForcing (changed.omega (index.val + 1) * length ^ 2)
          (fun patch => patchCentroid first time index patch) (quadrupoleCentroidForcing changed first time index) -
        fourPointTotalOddForcing (changed.omega (index.val + 1) * length ^ 2)
          (fun patch => patchCentroid second time index patch) (quadrupoleCentroidForcing changed second time index)‖ / length ≤
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + positions) +
        ‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / length +
        3 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
          quadrupoleExteriorCoefficient changed second index time radius power‖) := by
  have strainLimit : Tendsto (fun frequency : ℝ =>
      4 * (96 / Real.pi * (2304 * ({scales with frequency := frequency} : Scales).strain))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 2304).const_mul
      (96 / Real.pi)).const_mul 4
  filter_upwards [scales.eventually_cascade_prehit_odd_internal_small amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (le_trans (by norm_num) boundaryOne) thresholdSmall referenceNonnegative
      (show 0 < tolerance / 2 by positivity),
    scales.eventually_cascade_prehit_centered_exterior_return amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    strainLimit.eventually (eventually_lt_nhds (show 0 < tolerance / 2 by positivity))]
    with frequency internal external strainSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
    (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
  have lengthPositive : 0 < length := changed.length_pos _
  have positionsNonnegative : 0 ≤ positions := div_nonneg (norm_nonneg _) lengthPositive.le
  have internalBound := internal prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have externalBound := (external count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside).2
  dsimp only at internalBound externalBound
  rw [quadrupoleNormalizedCentroidOffsets_relative_norm_eq_div first second index time lengthPositive] at externalBound
  have enlarged := externalBound.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right strainSmall.le positionsNonnegative) _)
  have actual := div_le_div_of_nonneg_right (quadrupoleTotalOddForcing_relative_norm_split changed first second time index) lengthPositive.le
  rw [add_div, add_div] at actual
  have final := actual.trans (add_le_add_right (add_le_add internalBound enlarged) _)
  have momentNonnegative := norm_nonneg (relativeNormalizedFirstMoment changed first second index time)
  nlinarith only [final, mul_nonneg tolerancePositive.le momentNonnegative]

end EulerNonuniqueness.Paper
