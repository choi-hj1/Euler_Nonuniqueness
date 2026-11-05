import EulerNonuniqueness.Section5.CascadePrehitDilationInputRate
import EulerNonuniqueness.Section5.CascadeActualCentroidErrorArrayReturn

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_actual_prehit_dilation_return :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ),
      ∃ sourceConstant ≥ (0 : ℝ), ∃ receiverConstant ≥ (0 : ℝ), ∃ referenceErrorConstant ≥ (1 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ {scaleRoot boundaryConstant threshold referenceConstant factor tolerance : ℝ},
      1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 / 100 → 0 < tolerance →
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
      let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
      let radius := factor / 39321600 * changed.location (index.val + 1)
      let positionDifference :=
        ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
          (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
      |relativeDilationPhysicalVelocity changed first second index time| ≤
        tolerance * ‖relativeNormalizedFirstMoment changed first second index time‖ +
        (tolerance + 72 * (96 / Real.pi * (2304 * changed.strain)) +
          4 * referenceErrorConstant * changed.omega (index.val + 1) * epsilon) * positionDifference +
        36 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
          quadrupoleExteriorCoefficient changed second index time radius power‖) +
        12 * changed.omega (index.val + 1) * epsilon *
          ∑ patch : Fin 4, actualCentroidComparisonBudget changed
            (prepared.sourceComparison path ⟨inside.1, inside.2.trans finishBound⟩
              (finProdFinEquiv (index, patch)) (shapes patch))
            (index, patch) factor sourceConstant receiverConstant := by
  obtain ⟨sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, errorEstimates⟩ := exists_uniform_actual_centroid_error_array_return
  obtain ⟨referenceErrorConstant, referenceErrorOne, rates⟩ := exists_uniform_cascade_prehit_dilation_input_rate
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, referenceErrorConstant, referenceErrorOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant factor tolerance rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive
  filter_upwards [rates scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive,
    errorEstimates scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive
      (factorSmall.trans (by norm_num))] with frequency rate errors
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  obtain ⟨shapes, actualError⟩ := errors count orbit sectionTime phase dipoleAngle prepared path fullInside index
  refine ⟨shapes, ?_⟩
  have actualRate := rate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  dsimp only at actualRate actualError ⊢
  have enlarged := add_le_add_left (mul_le_mul_of_nonneg_left actualError (by norm_num : (0 : ℝ) ≤ 12))
    (tolerance * ‖relativeNormalizedFirstMoment {scales with frequency := frequency}
        prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖ +
      (tolerance + 72 * (96 / Real.pi * (2304 * ({scales with frequency := frequency} : Scales).strain)) +
        4 * referenceErrorConstant * ({scales with frequency := frequency} : Scales).omega (index.val + 1) *
          (({scales with frequency := frequency} : Scales).radius (index.val + 1) ^ 2 /
            ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2)) *
        (‖(fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
            quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index) -
          (fun patch => patchCentroid prepared.reference time index patch - quadrupoleCenter prepared.reference time index)‖ /
          ({scales with frequency := frequency} : Scales).length (index.val + 1)) +
      36 * (∑' power : ℕ, ‖quadrupoleExteriorCoefficient {scales with frequency := frequency}
          prepared.trajectory.movingFamily.patchMotion index time
          (factor / 39321600 * ({scales with frequency := frequency} : Scales).location (index.val + 1)) power -
        quadrupoleExteriorCoefficient {scales with frequency := frequency} prepared.reference index time
          (factor / 39321600 * ({scales with frequency := frequency} : Scales).location (index.val + 1)) power‖))
  exact (actualRate.trans enlarged).trans_eq (by ring)

end EulerNonuniqueness.Paper
