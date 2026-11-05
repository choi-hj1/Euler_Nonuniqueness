import EulerNonuniqueness.Section5.CascadeWeightedCenterClearance
import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry
import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000

theorem Scales.eventually_actual_cascade_source_comparison_geometry (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {threshold referenceConstant factor weight parameterRadius : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (weightPositive : 0 < weight) (parameterPositive : 0 < parameterRadius) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop,
      ∀ receiver source : Fin count × Fin 4, receiver ≠ source →
      let changed : Scales := {scales with frequency := frequency}
      let distance := (factor / 8) * changed.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1)
      let first := prepared.referenceWitness.trajectory.movingFamily
      let second := prepared.trajectory.movingFamily
      0 < distance ∧
      2 * (first.patch (finProdFinEquiv source)).radius + distance ≤
        ‖(first.patch (finProdFinEquiv receiver)).center time - (first.patch (finProdFinEquiv source)).center time‖ ∧
      2 * (first.patch (finProdFinEquiv source)).radius + distance ≤
        ‖(second.patch (finProdFinEquiv receiver)).center time - (second.patch (finProdFinEquiv source)).center time‖ ∧
      2 * weight * (first.patch (finProdFinEquiv receiver)).radius / distance ≤ 1 / 2 ∧
      96 * weight * (first.patch (finProdFinEquiv receiver)).radius /
        ‖(second.patch (finProdFinEquiv receiver)).center time - (second.patch (finProdFinEquiv source)).center time‖ ≤ 1 / 2 ∧
      (first.patch (finProdFinEquiv source)).radius /
        ‖(second.patch (finProdFinEquiv receiver)).center time - (second.patch (finProdFinEquiv source)).center time‖ ≤ parameterRadius := by
  filter_upwards [scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative,
    scales.eventually_weighted_comoving_center_ratios amplitudePositive ratioBound alphaPositive
      weightPositive factorPositive factorSmall parameterPositive,
    scales.eventually_radius_interaction_small amplitudePositive ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 16)]
    with frequency mechanical ratios radii
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant prepared path time inside receiver source different
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have referenceCenter (label : Fin count × Fin 4) :
      (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv label)).center time =
        patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time label.1 label.2 :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside label.1 label.2
  have alternativeCenter (label : Fin count × Fin 4) :
      (prepared.trajectory.movingFamily.patch (finProdFinEquiv label)).center time =
        prepared.trajectory.movingFamily.cascadeCenters time label := rfl
  have sourceRadius : (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv source)).radius =
      changed.radius (source.1.val + 1) := prepared.referenceWitness.radiusIdentity source.1 source.2
  have receiverRadius : (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv receiver)).radius =
      changed.radius (receiver.1.val + 1) := prepared.referenceWitness.radiusIdentity receiver.1 receiver.2
  have referenceGeometry := (mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
    prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside receiver.1).1
  have referenceLower := referenceGeometry.individual_center_distance receiver.2 source.1 source.2 different
  rw [← referenceCenter receiver, ← referenceCenter source] at referenceLower
  have interactionPositive := changed.individualInteractionDistance_pos (receiver.1.val + 1) (source.1.val + 1)
  have sourceSmall := (radii (receiver.1.val + 1) (source.1.val + 1)).2
  have weighted := ratios count (prepared.trajectory.movingFamily.cascadeCenters time)
    (path.internalClosed time inside)
    (fun label => (path.externalMonitors time inside (.extent label)).le)
    (fun first second => (path.externalMonitors time inside (.lower first second)).le)
    receiver source different
  have clearance := weighted.1
  change 2 * ((factor / 8) * changed.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1)) +
      3 * changed.radius (source.1.val + 1) <
      ‖prepared.trajectory.movingFamily.cascadeCenters time receiver - prepared.trajectory.movingFamily.cascadeCenters time source‖ at clearance
  rw [sourceRadius, receiverRadius, alternativeCenter, alternativeCenter]
  refine ⟨by positivity, ?_, ?_, weighted.2.1, weighted.2.2.1, weighted.2.2.2⟩
  · have scaleBound := mul_le_mul_of_nonneg_right factorSmall interactionPositive.le
    nlinarith only [referenceLower, sourceSmall, scaleBound, interactionPositive]
  · have radiusNonnegative : 0 ≤ changed.radius (source.1.val + 1) := Real.sqrt_nonneg _
    nlinarith only [clearance, radiusNonnegative, mul_pos factorPositive interactionPositive]

end EulerNonuniqueness.Paper
