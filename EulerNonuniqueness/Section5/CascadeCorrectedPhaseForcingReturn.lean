import EulerNonuniqueness.Section5.CascadeCorrectedPhaseForcingInput
import EulerNonuniqueness.Section5.CascadeActualCentroidErrorArrayReturn

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_actual_cascade_corrected_phase_forcing_return {correction : ℝ → ℝ}
    (correctionSmooth : ContDiffAt ℝ 2 correction 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
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
      (∀ side : Fin 2, |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| ≤ radius) →
      ∃ shapes : ∀ patch : Fin 4, ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let length := changed.length (index.val + 1)
      let virtualRadius := factor / 39321600 * changed.location (index.val + 1)
      let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
      |correctedPaperPhaseForcing changed correction first index time - correctedPaperPhaseForcing changed correction second index time| ≤
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + positions +
          |unstableShape first time index - unstableShape second time index|) +
        constant * (changed.omega (index.val + 1) * (changed.radius (index.val + 1) ^ 2 / length ^ 2) *
          (∑ patch : Fin 4, actualCentroidComparisonBudget changed
            (prepared.sourceComparison path ⟨inside.1, inside.2.trans finishBound⟩
              (finProdFinEquiv (index, patch)) (shapes patch))
            (index, patch) factor sourceConstant receiverConstant) +
          (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time virtualRadius power -
            quadrupoleExteriorCoefficient changed second index time virtualRadius power‖)) := by
  obtain ⟨radius, radiusPositive, radiusSmall, constant, constantOne, phaseEstimates⟩ :=
    exists_uniform_cascade_corrected_phase_forcing_input correctionSmooth
  obtain ⟨sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, errorEstimates⟩ := exists_uniform_actual_centroid_error_array_return
  refine ⟨radius, radiusPositive, radiusSmall, constant, constantOne, sourceRadius, sourcePositive,
    rawCap, rawPositive, sourceConstant, sourceNonnegative, receiverConstant, receiverNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant factor tolerance rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive
  filter_upwards [phaseEstimates scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive,
    errorEstimates scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive
      (factorSmall.trans (by norm_num))] with frequency phases errors
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside rawSmall
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  obtain ⟨shapes, actualError⟩ := errors count orbit sectionTime phase dipoleAngle prepared path fullInside index
  refine ⟨shapes, ?_⟩
  have actual := phases count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index nonterminal finish
    finishNonnegative finishBound radialSmall time inside rawSmall
  dsimp only at actual actualError ⊢
  apply actual.trans
  exact add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right actualError _)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) constantOne)) _

end EulerNonuniqueness.Paper
