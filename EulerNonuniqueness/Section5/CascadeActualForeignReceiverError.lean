import EulerNonuniqueness.Section5.CascadeForeignVirtualReceiverRadius
import EulerNonuniqueness.Section5.CascadeActualSourceComparison
import EulerNonuniqueness.Section3.MovingCanonicalCentroidResponseRelative
import EulerNonuniqueness.Section6.MovingForeignCentroidResponse

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 14000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_foreign_receiver_error_relative :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {threshold referenceConstant factor : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop), ∀ receiver : Fin count × Fin 4,
      ∃ shapes : ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      let changed : Scales := {scales with frequency := frequency}
      let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
      let selected := foreignQuadrupolePatchLabels receiver.1
      let virtualRadius := factor / 39321600 * changed.location (receiver.1.val + 1)
      ‖quadrupoleExternalReceiverResidual changed comparison.first.patchMotion time receiver.1 receiver.2 -
        quadrupoleExternalReceiverResidual changed comparison.second.patchMotion time receiver.1 receiver.2‖ ≤
        constant * (comparison.receiverRadius ^ 2 / virtualRadius) *
          ((∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
            ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver virtualRadius (power + 1) time‖) *
            (comparison.source (finProdFinEquiv receiver)).spectralDifferenceBudget +
          (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
            ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver virtualRadius (power + 1) time -
              comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver virtualRadius (power + 1) time‖) *
            ‖diskPhysicalTransverseProjection (comparison.final (finProdFinEquiv receiver))‖) := by
  obtain ⟨sourceRadius, sourcePositive, constant, nonnegative, bound⟩ :=
    exists_uniform_material_centroid_response_relative
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, nonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor thresholdSmall
    referenceNonnegative factorPositive factorSmall
  filter_upwards [scales.eventually_cascade_foreign_virtual_receiver_radius amplitudePositive ratioBound alphaPositive
    thresholdSmall referenceNonnegative factorPositive factorSmall] with frequency geometry
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant prepared path time inside receiver
  let shapes := actualShapes prepared path time inside
  refine ⟨shapes, ?_⟩
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let label := finProdFinEquiv receiver
  let selected := foreignQuadrupolePatchLabels receiver.1
  let virtualRadius := factor / 39321600 * changed.location (receiver.1.val + 1)
  let distance := factor / 1600 * changed.location (receiver.1.val + 1)
  have actualGeometry := geometry count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair
    path time inside receiver
  have virtualPositive : 0 < virtualRadius := actualGeometry.1
  have distancePositive : 0 < distance := actualGeometry.2.1
  have physicalSmall : comparison.receiverRadius ≤ virtualRadius := actualGeometry.2.2.1
  have small24 : 24 * virtualRadius / distance < 1 := actualGeometry.2.2.2.1
  have firstSeparated : ∀ source ∈ selected, ∀ position ∈ (comparison.first.patch source).domain time,
      distance ≤ ‖(comparison.first.patch label).center time - position‖ := actualGeometry.2.2.2.2.1
  have secondSeparated : ∀ source ∈ selected, ∀ position ∈ (comparison.second.patch source).domain time,
      distance ≤ ‖(comparison.second.patch label).center time - position‖ := actualGeometry.2.2.2.2.2.1
  have firstPhysicalSmall : 24 * (comparison.first.patch label).radius / distance < 1 :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left physicalSmall (by norm_num))
      distancePositive.le).trans_lt small24
  have secondPhysicalSmall : 24 * (comparison.second.patch label).radius / distance < 1 := by
    rw [← comparison.radiusEqual label]
    exact firstPhysicalSmall
  have initialArea : diskSpectralTubularArea (comparison.initial label) = Real.pi := by
    change contourAreaFunctional (diskPhysicalSpectralChart (comparison.initial label)) = Real.pi
    rw [← comparison.firstShape label]
    exact (shapes label).1.area
  have finalArea : diskSpectralTubularArea (comparison.final label) = Real.pi := by
    change contourAreaFunctional (diskPhysicalSpectralChart (comparison.final label)) = Real.pi
    rw [← comparison.secondShape label]
    exact (shapes label).2.area
  have actual := bound (count * 4) comparison.first comparison.second selected comparison.firstReceiver
    comparison.secondReceiver comparison.receiverRadius virtualRadius time
    (comparison.first.patch label).radius_positive virtualPositive physicalSmall
    (comparison.initial label) (comparison.final label)
    (mem_ball_zero_iff.mpr (shapes label).1.small) (mem_ball_zero_iff.mpr (shapes label).2.small)
    initialArea finalArea
    (by rw [← comparison.firstShape label]; exact (shapes label).1.centroid)
    (by rw [← comparison.secondShape label]; exact (shapes label).2.centroid)
    (Circle.exp ((comparison.first.patch label).phase time))
    actualGeometry.2.2.2.2.2.2.1 actualGeometry.2.2.2.2.2.2.2
  have firstResponse := comparison.first.quadrupoleExternalReceiverResidual_eq_foreign_centroid_response changed
    prepared.referenceWitness.densityIdentity prepared.referenceWitness.radiusIdentity receiver time
    distancePositive firstSeparated firstPhysicalSmall (shapes label).1.area (shapes label).1.centroid
  have secondResponse := comparison.second.quadrupoleExternalReceiverResidual_eq_foreign_centroid_response changed
    prepared.densityIdentity prepared.radiusIdentity receiver time
    distancePositive secondSeparated secondPhysicalSmall (shapes label).2.area (shapes label).2.centroid
  rw [firstResponse, secondResponse]
  have phaseIdentity : (comparison.second.patch (finProdFinEquiv receiver)).phase time =
      (comparison.first.patch (finProdFinEquiv receiver)).phase time :=
    (comparison.phaseEqual (finProdFinEquiv receiver)).symm
  rw [← comparison.radiusEqual (finProdFinEquiv receiver), phaseIdentity]
  simpa only [← comparison.firstShape label, ← comparison.secondShape label,
    MovingPatchSourceComparison.spectralDifferenceBudget, MovingPatchFamilySourceComparison.source,
    comparison, label, selected, virtualRadius] using actual

end EulerNonuniqueness.Paper
