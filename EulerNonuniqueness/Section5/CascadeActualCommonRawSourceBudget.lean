import EulerNonuniqueness.Section5.CascadeActualCommonBoundaryRecord
import EulerNonuniqueness.Section3.CanonicalExteriorCommonRawSourceBudget

noncomputable section

open Set Filter

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

open FiniteMovingPatchFamily

theorem exists_uniform_actual_common_raw_source_budget :
    ∃ constant ≥ (1 : ℝ), ∃ rawCap > 0, ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ radiusCoefficient ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {requestedCap shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair requestedCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      0 < requestedCap → requestedCap ≤ rawCap →
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ time ∈ Icc 0 path.stop, ∀ (index : Fin count) (patch : Fin 4),
      let changed : Scales := {scales with frequency := frequency}
      let label := finProdFinEquiv (index, patch)
      let first := prepared.referenceWitness.trajectory.spectralCoordinate label time
      let final := prepared.trajectory.spectralCoordinate label time
      ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
        (‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖) *
          ‖diskNeutralCLM first - diskNeutralCLM final‖ ≤
      constant * prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonBoundaryDistance label
        (patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) time
        (radiusCoefficient / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2)) first final := by
  obtain ⟨caps, constant, constantOne, budgets⟩ := exists_canonical_common_boundary_raw_source_budget
  obtain ⟨rawCap, rawPositive, parameters⟩ := exists_uniform_actual_common_boundary_record caps
  refine ⟨constant, constantOne, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨coefficient, coefficientOne, rootMin, rootEight, records⟩ := parameters factor factorPositive factorSmall
  refine ⟨coefficient, coefficientOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  filter_upwards [records scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive
    threshold referenceConstant thresholdSmall referenceNonnegative] with frequency actual
  intro count orbit sectionTime phase dipoleAngle requestedCap shapeRadius monitor boundaryConstant prepared requestedPositive requestedSmall path time inside index patch
  have comparison := by
    with_reducible_and_instances
      exact actual count orbit sectionTime phase dipoleAngle prepared requestedPositive requestedSmall path time inside index patch
  have bound := budgets prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily
    (finProdFinEquiv (index, patch)) (finProdFinEquiv (index, patch))
    (patchSign patch * scales.amplitude * ({scales with frequency := frequency}).omega (index.val + 1) ^ 4) time
    (({scales with frequency := frequency}).length (index.val + 1) / 400)
    (factor * ({scales with frequency := frequency}).length (index.val + 1) / 400)
    (({scales with frequency := frequency}).referenceLocalExteriorWeight (index.val + 1))
    (2 * ({scales with frequency := frequency}).circulation (index.val + 1))
    (coefficient / (scaleRoot ^ 2 * ({scales with frequency := frequency}).omega (index.val + 1) ^ 2))
    (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)
    (prepared.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time) comparison
  with_reducible_and_instances
    simpa only [CanonicalCommonBoundaryPairAt.boundaryDistance, canonicalExteriorCommonBoundaryDistance] using bound

end EulerNonuniqueness.Paper
