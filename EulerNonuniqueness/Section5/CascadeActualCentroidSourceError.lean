import EulerNonuniqueness.Section5.CascadeActualQuadrupoleComparison
import EulerNonuniqueness.Section5.CascadeActualSourceGeometry
import EulerNonuniqueness.Section6.MovingPatchVelocityEndpoint

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_centroid_source_error_relative :
    ∃ sourceRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {threshold referenceConstant factor : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {rawCap scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop),
      ∀ shapes : ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      ∀ receiver : Fin count × Fin 4,
      ∀ selected : Finset (Fin (count * 4)), selected ⊆ Finset.univ.erase (finProdFinEquiv receiver) →
      let changed : Scales := {scales with frequency := frequency}
      let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
      let distance := fun label : Fin (count * 4) => (factor / 8) *
        changed.individualInteractionDistance (receiver.1.val + 1) ((finProdFinEquiv.symm label).1.val + 1)
      ‖∑ label ∈ selected,
        (comparison.source label).velocityCentroidCorrectionDifference‖ ≤
      ∑ label ∈ selected,
        ((comparison.source label).velocityCentroidCorrectionCenterEnvelope (distance label) +
          (comparison.source label).velocityCentroidCorrectionShapeEnvelope constant) := by
  obtain ⟨sourceRadius, sourcePositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    MovingPatchSourceComparison.velocityCentroidCorrection_endpoint_exists_centered_relative_bound
  refine ⟨sourceRadius, sourcePositive, constant, nonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor thresholdSmall
    referenceNonnegative factorPositive factorSmall
  filter_upwards [scales.eventually_actual_cascade_source_comparison_geometry amplitudePositive ratioBound alphaPositive
    thresholdSmall referenceNonnegative factorPositive factorSmall (weight := 1) (by norm_num) parameterPositive]
    with frequency geometry
  intro count orbit sectionTime phase dipoleAngle rawCap scaleRoot shapeRadius monitor boundaryConstant
    prepared path time inside shapes receiver selected subset
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro label member
  let source := finProdFinEquiv.symm label
  have sourceIdentity : finProdFinEquiv source = label := finProdFinEquiv.apply_symm_apply label
  have different : receiver ≠ source := by
    intro equality
    have labelEqual : label = finProdFinEquiv receiver := by rw [← sourceIdentity, ← equality]
    exact (Finset.mem_erase.mp (subset member)).1 labelEqual
  have actualGeometry := geometry count orbit sectionTime phase dipoleAngle
    prepared.toCascadeMaterialPreparedPair path time inside receiver source different
  have states := prepared.sourceComparison_states path inside (finProdFinEquiv receiver) shapes label
  apply bound (comparison.source label) states.1 states.2.1 states.2.2.1 states.2.2.2
    (prepared.sourceComparison_first_true_centers path inside (finProdFinEquiv receiver) shapes label)
    ((factor / 8) * changed.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1))
    actualGeometry.1
  · simpa only [comparison, MovingPatchFamilySourceComparison.source, sourceIdentity] using actualGeometry.2.1
  · simpa only [comparison, MovingPatchFamilySourceComparison.source, sourceIdentity] using actualGeometry.2.2.1
  · simpa only [comparison, MovingPatchFamilySourceComparison.source, sourceIdentity] using actualGeometry.2.2.2.2.2

end EulerNonuniqueness.Paper
