import EulerNonuniqueness.Section6.PaperOddForcingNormSplit
import EulerNonuniqueness.Section5.CascadePrehitOddInternalAbsolute
import EulerNonuniqueness.Section5.CascadePrehitCenteredExteriorAbsolute
import EulerNonuniqueness.Section5.CascadeStoppedPatchErrorSmall

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_cascade_prehit_total_odd_forcing_small (scales : Scales)
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
      let motion := prepared.trajectory.movingFamily.patchMotion
      ‖fourPointTotalOddForcing (changed.omega (index.val + 1) * changed.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid motion time index patch) (quadrupoleCentroidForcing changed motion time index)‖ /
        changed.length (index.val + 1) ≤ tolerance := by
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := le_trans (by norm_num) boundaryOne
  have thirdPositive : 0 < tolerance / 3 := by positivity
  have strainLimit : Tendsto (fun frequency : ℝ =>
      42 * (96 / Real.pi * (2304 * ({scales with frequency := frequency} : Scales).strain))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 2304).const_mul
      (96 / Real.pi)).const_mul 42
  filter_upwards [scales.eventually_cascade_prehit_odd_internal_absolute_small amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative thresholdSmall referenceNonnegative thirdPositive,
    scales.eventually_cascade_stopped_patch_error_small amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      factorPositive (factorSmall.trans (by norm_num)) thirdPositive,
    scales.eventually_cascade_prehit_centered_exterior_absolute amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    strainLimit.eventually (eventually_lt_nhds thirdPositive)] with frequency internal errors external strainSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have internalBound := internal prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have errorBound := errors prepared path time fullInside index
  have externalBound := (external count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside).trans
    strainSmall.le
  dsimp only at internalBound errorBound
  have actual := div_le_div_of_nonneg_right
    (quadrupoleTotalOddForcing_norm_split {scales with frequency := frequency}
      prepared.trajectory.movingFamily.patchMotion time index)
    (({scales with frequency := frequency} : Scales).length_pos (index.val + 1)).le
  rw [add_div, add_div] at actual
  exact actual.trans (by linarith)

end EulerNonuniqueness.Paper
