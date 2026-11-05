import EulerNonuniqueness.Section5.CascadePrehitInternalCenterSmall
import EulerNonuniqueness.Section5.CascadeCenterVelocityArrayBound
import EulerNonuniqueness.Section5.CascadeActualCentroidErrorArrayReturn

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_actual_prehit_center_return :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ),
      ∃ sourceConstant ≥ (0 : ℝ), ∃ receiverConstant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {scaleRoot boundaryConstant threshold referenceConstant factor tolerance : ℝ},
      0 < scaleRoot → 0 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 / 100 → 0 < tolerance →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → ∀ finishBound : finish ≤ path.stop,
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time (inside : time ∈ Icc 0 finish),
      ∃ shapes : ∀ patch : Fin 4, ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let length := changed.length (index.val + 1)
      let location := changed.location (index.val + 1)
      ‖prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 0 index time -
          prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 1 index time‖ / location ≤
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ +
          ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
            (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length) +
        (∑ patch : Fin 4,
          ‖biotSavart (externalPatchVorticity changed first time index) (patchCentroid first time index patch) -
            biotSavart (externalPatchVorticity changed second time index) (patchCentroid second time index patch)‖) /
          (4 * location) +
        (changed.omega (index.val + 1) * length / location) * (changed.radius (index.val + 1) ^ 2 / length ^ 2) *
          ∑ patch : Fin 4, actualCentroidComparisonBudget changed
            (prepared.sourceComparison path ⟨inside.1, inside.2.trans finishBound⟩
              (finProdFinEquiv (index, patch)) (shapes patch))
            (index, patch) factor sourceConstant receiverConstant := by
  obtain ⟨sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, errors⟩ := exists_uniform_actual_centroid_error_array_return
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant threshold referenceConstant factor
    tolerance rootPositive boundaryNonnegative thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive
  filter_upwards [scales.eventually_cascade_prehit_internal_center_small amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive,
    errors scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive
      (factorSmall.trans (by norm_num))] with frequency internal errorBounds
  intro count orbit sectionTime phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  obtain ⟨shapes, errorBound⟩ := errorBounds count orbit sectionTime phase dipoleAngle prepared path fullInside index
  refine ⟨shapes, ?_⟩
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let location := changed.location (index.val + 1)
  have lengthPositive : 0 < length := changed.length_pos _
  have locationPositive : 0 < location := changed.location_pos _
  have internalBound := internal prepared.toCascadeMaterialPreparedPair path index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  have mechanical := path.paired_center_velocity_difference_norm_le_array fullInside index
  have divided := div_le_div_of_nonneg_right mechanical locationPositive.le
  rw [add_div, add_div] at divided
  have errorNormalized :
      ‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / location ≤
        (changed.omega (index.val + 1) * length / location) * (changed.radius (index.val + 1) ^ 2 / length ^ 2) *
          ∑ patch : Fin 4, actualCentroidComparisonBudget changed
            (prepared.sourceComparison path fullInside (finProdFinEquiv (index, patch)) (shapes patch))
            (index, patch) factor sourceConstant receiverConstant := by
    calc
      _ = (length / location) *
          (‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / length) := by
        field_simp
        <;> ring
      _ ≤ (length / location) * _ := mul_le_mul_of_nonneg_left errorBound (by positivity)
      _ = _ := by ring
  exact (divided.trans (add_le_add (add_le_add_right internalBound _) errorNormalized)).trans_eq (by ring)

end EulerNonuniqueness.Paper
