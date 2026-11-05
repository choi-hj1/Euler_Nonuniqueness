import EulerNonuniqueness.Section5.CascadeActualCentroidSourceError
import EulerNonuniqueness.Section6.MovingPatchVelocityReturnScale

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

namespace CascadeSourcePreparedPair

variable {rawCap sourceRadius : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
  {count : ℕ}

theorem sourceComparison_source_absolute_mass_radius
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (source : Fin count × Fin 4) :
    let comparison := (prepared.sourceComparison path inside receiver shapes).source (finProdFinEquiv source)
    |comparison.density| * comparison.first.radius ^ 2 =
      2 * scales.omega (source.1.val + 1) * scales.length (source.1.val + 1) ^ 2 := by
  dsimp only
  change |prepared.referenceWitness.configuration.density (finProdFinEquiv source)| *
    prepared.referenceWitness.configuration.radius (finProdFinEquiv source) ^ 2 = _
  rw [prepared.referenceWitness.densityIdentity, prepared.referenceWitness.radiusIdentity,
    abs_mul, abs_mul, abs_of_pos amplitudePositive,
    abs_of_pos (pow_pos (scales.omega_pos frequencyPositive ratioPositive _) _)]
  have sign : |patchSign source.2| = 1 := by
    unfold patchSign
    split <;> norm_num
  rw [sign, one_mul, scales.radius_sq amplitudePositive frequencyPositive ratioPositive]
  field_simp [(scales.omega_pos frequencyPositive ratioPositive (source.1.val + 1)).ne', amplitudePositive.ne']
  <;> ring

end CascadeSourcePreparedPair

theorem exists_uniform_actual_own_centroid_source_return :
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
      let changed : Scales := {scales with frequency := frequency}
      let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
      let selected := (Finset.univ.erase (finProdFinEquiv receiver)).filter
        (fun label => (finProdFinEquiv.symm label).1 = receiver.1)
      ‖∑ label ∈ selected, (comparison.source label).velocityCentroidCorrectionDifference‖ /
          (changed.omega (receiver.1.val + 1) * changed.length (receiver.1.val + 1)) ≤
        (changed.radius (receiver.1.val + 1) ^ 2 / changed.length (receiver.1.val + 1) ^ 2) *
          ∑ label ∈ selected,
            (24 * (factor / 800)⁻¹ ^ 4 *
                (‖(comparison.source label).displacementDifference‖ / changed.length (receiver.1.val + 1)) +
              96 * constant / Real.pi * (factor / 800)⁻¹ ^ 3 *
                (comparison.source label).spectralDifferenceBudget) := by
  obtain ⟨sourceRadius, sourcePositive, constant, nonnegative, bound⟩ :=
    exists_uniform_actual_centroid_source_error_relative
  refine ⟨sourceRadius, sourcePositive, constant, nonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor thresholdSmall
    referenceNonnegative factorPositive factorSmall
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    bound scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive factorSmall,
    scales.eventually_actual_cascade_source_comparison_geometry amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall (weight := 1) (by norm_num)
      (parameterRadius := 1) (by norm_num)] with frequency frequencyPositive actualBound geometry
  intro count orbit sectionTime phase dipoleAngle rawCap scaleRoot shapeRadius monitor boundaryConstant
    prepared path time inside shapes receiver
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let selected := (Finset.univ.erase (finProdFinEquiv receiver)).filter
    (fun label => (finProdFinEquiv.symm label).1 = receiver.1)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaPositive : 0 < changed.omega (receiver.1.val + 1) := changed.omega_pos frequencyPositive ratioPositive _
  have lengthPositive := changed.length_pos (receiver.1.val + 1)
  have denominatorPositive := mul_pos omegaPositive lengthPositive
  have subset : selected ⊆ Finset.univ.erase (finProdFinEquiv receiver) := Finset.filter_subset _ _
  have actual := actualBound count orbit sectionTime phase dipoleAngle prepared path inside shapes receiver selected subset
  change ‖∑ label ∈ selected, (comparison.source label).velocityCentroidCorrectionDifference‖ ≤
    ∑ label ∈ selected, ((comparison.source label).velocityCentroidCorrectionCenterEnvelope
      ((factor / 8) * changed.individualInteractionDistance (receiver.1.val + 1)
        ((finProdFinEquiv.symm label).1.val + 1)) +
      (comparison.source label).velocityCentroidCorrectionShapeEnvelope constant) at actual
  apply (div_le_div_of_nonneg_right actual denominatorPositive.le).trans
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro label member
  let source := finProdFinEquiv.symm label
  have same : source.1 = receiver.1 := (Finset.mem_filter.mp member).2
  have sourceIdentity : finProdFinEquiv source = label := finProdFinEquiv.apply_symm_apply label
  have different : receiver ≠ source := by
    intro equality
    have labelEqual : label = finProdFinEquiv receiver := by rw [← sourceIdentity, ← equality]
    exact (Finset.mem_erase.mp (subset member)).1 labelEqual
  have actualGeometry := geometry count orbit sectionTime phase dipoleAngle
    prepared.toCascadeMaterialPreparedPair path time inside receiver source different
  have distanceIdentity : (factor / 8) * changed.individualInteractionDistance
      (receiver.1.val + 1) (source.1.val + 1) = (factor / 800) * changed.length (receiver.1.val + 1) := by
    rw [same]
    unfold Scales.individualInteractionDistance
    simp only [ite_true]
    ring
  have sourceRadius : (comparison.source label).first.radius = changed.radius (receiver.1.val + 1) := by
    change prepared.referenceWitness.configuration.radius label = _
    rw [← sourceIdentity, prepared.referenceWitness.radiusIdentity source.1 source.2, same]
  have mass := prepared.sourceComparison_source_absolute_mass_radius path inside
    (finProdFinEquiv receiver) shapes amplitudePositive frequencyPositive ratioPositive source
  rw [sourceIdentity, same] at mass
  have separation : (factor / 800) * changed.length (receiver.1.val + 1) ≤
      ‖(comparison.source label).secondReceiver - (comparison.source label).second.center comparison.time‖ := by
    have lower := actualGeometry.2.2.1
    rw [distanceIdentity] at lower
    have transferred : 2 * (comparison.source label).first.radius +
        (factor / 800) * changed.length (receiver.1.val + 1) ≤
        ‖(comparison.source label).secondReceiver - (comparison.source label).second.center comparison.time‖ := by
      simpa only [comparison, MovingPatchFamilySourceComparison.source, sourceIdentity] using lower
    linarith [(comparison.source label).first.radius_positive.le]
  rw [distanceIdentity]
  have normalized := (comparison.source label).velocityCentroidCorrection_envelopes_normalized_le
    omegaPositive lengthPositive (by positivity : 0 < factor / 800) nonnegative mass separation
  rw [sourceRadius] at normalized
  exact normalized

end EulerNonuniqueness.Paper
