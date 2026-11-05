import EulerNonuniqueness.Section5.CascadePrehitRelativeShapeForcingInput
import EulerNonuniqueness.Section5.CascadeActualCentroidErrorArrayReturn

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_actual_prehit_relative_shape_forcing_return :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ),
      ∃ sourceConstant ≥ (0 : ℝ), ∃ receiverConstant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ {scaleRoot boundaryConstant threshold referenceConstant factor tolerance : ℝ},
      1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 / 8 → 0 < tolerance →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
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
      let radius := factor / 39321600 * changed.location (index.val + 1)
      let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
      ‖referencePointShapeForcing changed first time index - referencePointShapeForcing changed second time index -
          quadrupoleRelativeLeadingStrain changed first second time index‖ ≤
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + positions) +
        30 * (changed.omega (index.val + 1) * (changed.radius (index.val + 1) ^ 2 / length ^ 2) *
          ∑ patch : Fin 4, actualCentroidComparisonBudget changed
            (prepared.sourceComparison path ⟨inside.1, inside.2.trans finishBound⟩
              (finProdFinEquiv (index, patch)) (shapes patch))
            (index, patch) factor sourceConstant receiverConstant) +
        30 * ((length / radius) * (6 * (96 / Real.pi * (2304 * changed.strain)) * positions +
          9 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius (power + 1) -
            quadrupoleExteriorCoefficient changed second index time radius (power + 1)‖))) := by
  obtain ⟨sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, errorEstimates⟩ := exists_uniform_actual_centroid_error_array_return
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant factor tolerance rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive
  filter_upwards [scales.eventually_cascade_prehit_relative_shape_forcing_input amplitudePositive ratioBound alphaPositive
      orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive,
    errorEstimates scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive
      (factorSmall.trans (by norm_num))] with frequency forcing errors
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  obtain ⟨shapes, actualError⟩ := errors count orbit sectionTime phase dipoleAngle prepared path fullInside index
  refine ⟨shapes, ?_⟩
  have actual := forcing count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  dsimp only at actual actualError ⊢
  apply actual.trans
  exact add_le_add_right (add_le_add_left
    (mul_le_mul_of_nonneg_left actualError (by norm_num : (0 : ℝ) ≤ 30)) _) _

end EulerNonuniqueness.Paper
