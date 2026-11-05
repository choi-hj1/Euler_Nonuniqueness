import EulerNonuniqueness.Section5.CascadeActualSourceComparison
import EulerNonuniqueness.Section5.CascadeVirtualReceiverRadius
import EulerNonuniqueness.Section3.MovingCanonicalCentroidResponseRelative

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_centroid_receiver_error_relative :
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
      ∀ receiver : Fin count × Fin 4, ∀ commonPhase : Circle,
      let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
      let selected := Finset.univ.erase (finProdFinEquiv receiver)
      let virtualRadius := factor / 39321600 * ({scales with frequency := frequency} : Scales).length (receiver.1.val + 1)
      ‖comparison.receiverRadius • ((commonPhase : ℂ) *
          contourExteriorCentroidResponse commonPhase
            (fun power => comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver
              comparison.receiverRadius (power + 1) time)
            ((prepared.referenceWitness.trajectory.curve time).2.2 (finProdFinEquiv receiver))) -
        comparison.receiverRadius • ((commonPhase : ℂ) *
          contourExteriorCentroidResponse commonPhase
            (fun power => comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver
              comparison.receiverRadius (power + 1) time)
            ((prepared.trajectory.curve time).2.2 (finProdFinEquiv receiver)))‖ ≤
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
  refine ⟨sourceRadius, sourcePositive, constant, nonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor thresholdSmall
    referenceNonnegative factorPositive factorSmall
  filter_upwards [scales.eventually_cascade_virtual_receiver_radius amplitudePositive ratioBound alphaPositive
    thresholdSmall referenceNonnegative factorPositive factorSmall] with frequency geometry
  intro count orbit sectionTime phase dipoleAngle rawCap scaleRoot shapeRadius monitor boundaryConstant
    prepared path time inside shapes receiver commonPhase
  dsimp only
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let selected := Finset.univ.erase (finProdFinEquiv receiver)
  let virtualRadius := factor / 39321600 * ({scales with frequency := frequency} : Scales).length (receiver.1.val + 1)
  let label := finProdFinEquiv receiver
  have actualGeometry := geometry count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair
    path time inside receiver
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
    ((comparison.first.patch label).radius_positive) actualGeometry.1 actualGeometry.2.2.1
    (comparison.initial label) (comparison.final label)
    (mem_ball_zero_iff.mpr (shapes label).1.small) (mem_ball_zero_iff.mpr (shapes label).2.small)
    initialArea finalArea
    (by rw [← comparison.firstShape label]; exact (shapes label).1.centroid)
    (by rw [← comparison.secondShape label]; exact (shapes label).2.centroid)
    commonPhase actualGeometry.2.2.2.2.2.1 actualGeometry.2.2.2.2.2.2
  simpa only [← comparison.firstShape label, ← comparison.secondShape label,
    MovingPatchSourceComparison.spectralDifferenceBudget, MovingPatchFamilySourceComparison.source,
    comparison, label, selected, virtualRadius] using actual

end EulerNonuniqueness.Paper
