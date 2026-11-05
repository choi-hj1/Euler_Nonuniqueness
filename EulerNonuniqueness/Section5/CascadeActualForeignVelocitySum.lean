import EulerNonuniqueness.Section5.CascadeActualQuadrupoleVelocity
import EulerNonuniqueness.Section6.MovingForeignVelocitySum

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 14000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_foreign_velocity_difference_sum :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
      threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
      0 < factor → factor ≤ 1 →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop), ∀ receiver : Fin count × Fin 4,
      ∃ shapes : ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      let changed : Scales := {scales with frequency := frequency}
      let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
      ‖biotSavart (externalPatchVorticity changed comparison.first.patchMotion time receiver.1)
          (patchCentroid comparison.first.patchMotion time receiver.1 receiver.2) -
        biotSavart (externalPatchVorticity changed comparison.second.patchMotion time receiver.1)
          (patchCentroid comparison.second.patchMotion time receiver.1 receiver.2)‖ ≤
      ∑ source ∈ Finset.univ.erase receiver.1,
        ((comparison.quadrupole source).quadrupoleVelocityPointDifferenceEnvelope
          (changed.circulation (source.val + 1))
          (quadrupoleCenter comparison.first.patchMotion time source)
          (quadrupoleCenter comparison.second.patchMotion time source)
          (changed.location (source.val + 1) / 100)
          (|changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8) +
        ∑ patch : Fin 4,
          (((comparison.quadrupole source).source patch).velocityCentroidCorrectionCenterEnvelope
              (|changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8) +
            ((comparison.quadrupole source).source patch).velocityCentroidCorrectionShapeEnvelope constant)) := by
  obtain ⟨sourceRadius, sourcePositive, constant, nonnegative, bound⟩ :=
    exists_uniform_actual_foreign_quadrupole_relative_velocity
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, nonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot
    factor boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [bound scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall
      referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall]
    with frequency bounds alignment
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  let shapes := actualShapes prepared path time inside
  refine ⟨shapes, ?_⟩
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have firstCenter : comparison.firstReceiver time = patchCentroid comparison.first.patchMotion time receiver.1 receiver.2 :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver.1 receiver.2
  have secondCenter : comparison.secondReceiver time = patchCentroid comparison.second.patchMotion time receiver.1 receiver.2 :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver.1 receiver.2
  have firstSum := comparison.first.externalPatch_biotSavart_eq_sum_quadrupoles changed
    prepared.referenceWitness.densityIdentity time receiver.1 (comparison.firstReceiver time)
  have secondSum := comparison.second.externalPatch_biotSavart_eq_sum_quadrupoles changed
    prepared.densityIdentity time receiver.1 (comparison.secondReceiver time)
  rw [← firstCenter, ← secondCenter, firstSum, secondSum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro source member
  have different : receiver.1 ≠ source := Ne.symm (Finset.mem_erase.mp member).1
  have actualAlignment := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver source different
  have actual := bounds count phase dipoleAngle prepared path inside shapes receiver source different
    (changed.location (source.val + 1) / 100)
    (div_nonneg (changed.location_pos (source.val + 1)).le (by norm_num))
    le_rfl actualAlignment.2.2.1 actualAlignment.2.2.2
  exact actual

end EulerNonuniqueness.Paper
