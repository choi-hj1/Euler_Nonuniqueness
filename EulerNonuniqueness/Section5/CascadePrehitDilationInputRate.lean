import EulerNonuniqueness.Section5.CascadePrehitInternalDilationSmall
import EulerNonuniqueness.Section5.CascadePrehitExternalDilationReturn
import EulerNonuniqueness.Section5.CascadePrehitPatchDilationReturn
import EulerNonuniqueness.Section5.CascadeReferencePatchErrorBound
import EulerNonuniqueness.Section5.CascadeDilationPhysicalHistory

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_cascade_prehit_dilation_input_rate :
    ∃ constant ≥ (1 : ℝ), ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ {scaleRoot boundaryConstant threshold referenceConstant factor tolerance : ℝ},
      1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 / 100 → 0 < tolerance →
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
      let positionDifference :=
        ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
          (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
      |relativeDilationPhysicalVelocity changed first second index time| ≤
        tolerance * ‖relativeNormalizedFirstMoment changed first second index time‖ +
        (tolerance + 72 * (96 / Real.pi * (2304 * changed.strain)) +
          4 * constant * changed.omega (index.val + 1) * (changed.radius (index.val + 1) ^ 2 / length ^ 2)) *
            positionDifference +
        36 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
          quadrupoleExteriorCoefficient changed second index time radius power‖) +
        12 * (‖quadrupoleDilationPatchError changed first index time -
          quadrupoleDilationPatchError changed second index time‖ / length) := by
  obtain ⟨constant, constantOne, referenceErrors⟩ := exists_uniform_cascade_reference_patch_error_bound
  refine ⟨constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant factor tolerance rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  filter_upwards [scales.eventually_cascade_prehit_internal_dilation_small amplitudePositive ratioBound alphaPositive
      (by linarith : 0 < scaleRoot) (by linarith : 0 ≤ boundaryConstant) thresholdSmall referenceNonnegative
      factorPositive factorSmall tolerancePositive,
    scales.eventually_cascade_prehit_external_dilation_return amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorEighth,
    scales.eventually_cascade_prehit_patch_dilation_return amplitudePositive ratioBound alphaPositive
      (by linarith : 0 < scaleRoot) (by linarith : 0 ≤ boundaryConstant) thresholdSmall referenceNonnegative,
    referenceErrors scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative]
    with frequency internal external patch referenceError
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let difference := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
    (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
  have lengthPositive : 0 < length := changed.length_pos _
  have differenceNonnegative : 0 ≤ difference := div_nonneg (norm_nonneg _) lengthPositive.le
  have pointBound := internal prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have externalBound := external count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have patchBound := patch prepared path factorEighth index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
  have referenceBound := referenceError count orbit sectionTime phase dipoleAngle prepared time referenceInside index
  dsimp only at pointBound externalBound patchBound referenceBound
  have patchEnlarged := mul_le_mul_of_nonneg_left referenceBound (show 0 ≤ 4 * difference by positivity)
  have patchFinal := patchBound.trans (add_le_add_right patchEnlarged _)
  have triangle := (abs_add (quadrupoleInternalDilationRate changed first index time -
      quadrupoleInternalDilationRate changed second index time +
      (quadrupoleExternalDilationRate changed first index time - quadrupoleExternalDilationRate changed second index time))
      (quadrupolePatchDilationRate changed first index time - quadrupolePatchDilationRate changed second index time)).trans
    (add_le_add_right (abs_add _ _) _)
  have divided := div_le_div_of_nonneg_right triangle (sq_nonneg length)
  rw [add_div, add_div] at divided
  have combined := divided.trans (add_le_add (add_le_add pointBound externalBound) patchFinal)
  change |relativeDilationPhysicalVelocity changed first second index time| ≤ _
  rw [relativeDilationPhysicalVelocity, abs_div, abs_of_pos (sq_pos_of_pos lengthPositive)]
  exact combined.trans_eq (by dsimp only [difference]; ring)

end EulerNonuniqueness.Paper
