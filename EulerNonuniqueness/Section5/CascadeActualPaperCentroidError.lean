import EulerNonuniqueness.Section5.CascadeVirtualReceiverRadius
import EulerNonuniqueness.Section6.MovingQuadrupoleCentroidResponse

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem Scales.eventually_cascade_actual_paper_centroid_error (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {threshold referenceConstant factor : ℝ} (thresholdSmall : threshold ≤ 1 / 8)
    (referenceNonnegative : 0 ≤ referenceConstant) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop,
      ∀ receiver : Fin count × Fin 4,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.referenceWitness.trajectory.movingFamily
      let second := prepared.trajectory.movingFamily
      (quadrupoleInternalPatchResidual changed second.patchMotion time receiver.1 receiver.2 +
        quadrupoleExternalReceiverResidual changed second.patchMotion time receiver.1 receiver.2) -
        (quadrupoleInternalPatchResidual changed prepared.reference time receiver.1 receiver.2 +
          quadrupoleExternalReceiverResidual changed prepared.reference time receiver.1 receiver.2) =
        (second.ownSourceCentroidCorrection receiver time - first.ownSourceCentroidCorrection receiver time) +
          (second.receivingCentroidResponse (finProdFinEquiv receiver) time -
            first.receivingCentroidResponse (finProdFinEquiv receiver) time) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_cascade_virtual_receiver_radius amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall] with frequency frequencyPositive geometry
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant prepared path time inside receiver
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily
  let second := prepared.trajectory.movingFamily
  let virtualRadius := factor / 39321600 * changed.length (receiver.1.val + 1)
  let distance := factor / 1600 * changed.length (receiver.1.val + 1)
  have actualGeometry := geometry count orbit sectionTime phase dipoleAngle prepared path time inside receiver
  have distancePositive : 0 < distance := actualGeometry.2.1
  have firstPhysical : (first.patch (finProdFinEquiv receiver)).radius ≤ virtualRadius := actualGeometry.2.2.1
  have radiusEqual : (second.patch (finProdFinEquiv receiver)).radius =
      (first.patch (finProdFinEquiv receiver)).radius := by
    change prepared.configuration.radius (finProdFinEquiv receiver) =
      prepared.referenceWitness.configuration.radius (finProdFinEquiv receiver)
    rw [prepared.radiusIdentity receiver.1 receiver.2, prepared.referenceWitness.radiusIdentity receiver.1 receiver.2]
  have secondPhysical : (second.patch (finProdFinEquiv receiver)).radius ≤ virtualRadius := by
    rw [radiusEqual]
    exact firstPhysical
  have small (radius : ℝ) (radiusSmall : radius ≤ virtualRadius) : 8 * radius ≤ distance := by
    have positiveProduct := mul_pos factorPositive (changed.length_pos (receiver.1.val + 1))
    dsimp only [virtualRadius, distance] at radiusSmall ⊢
    nlinarith
  have ratio (radius : ℝ) (radiusSmall : radius ≤ virtualRadius) : 24 * radius / distance < 1 := by
    apply (div_lt_one distancePositive).mpr
    have positiveProduct := mul_pos factorPositive (changed.length_pos (receiver.1.val + 1))
    dsimp only [virtualRadius, distance] at radiusSmall ⊢
    nlinarith
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have referenceArea := prepared.referenceWitness.trajectory.shape_area_eq_pi_of_margin
    (fun _ => rfl) prepared.referenceWitness.marginPositive referenceInside (by norm_num)
    prepared.referenceWitness.safe (finProdFinEquiv receiver)
  have alternativeArea := prepared.trajectory.shape_area_eq_pi_of_margin (fun _ => rfl)
    prepared.marginPositive inside (by linarith [path.stopBound])
    (fun current member => (path.safe current member).le) (finProdFinEquiv receiver)
  have firstEquation := prepared.referenceWitness.trajectory.paperCentroidResidual_eq_source_and_response
    (scales := changed) rfl (fun _ => rfl) prepared.referenceWitness.marginPositive amplitudePositive frequencyPositive
    (show 0 < changed.ratio by change 0 < scales.ratio; linarith) prepared.referenceWitness.densityIdentity
    prepared.referenceWitness.evolution globalInside referenceInside prepared.referenceWitness.safe receiver distancePositive
    (small _ firstPhysical) actualGeometry.2.2.2.1 referenceArea (ratio _ firstPhysical)
  have secondEquation := prepared.trajectory.paperCentroidResidual_eq_source_and_response
    (scales := changed) rfl (fun _ => rfl) prepared.marginPositive amplitudePositive frequencyPositive
    (show 0 < changed.ratio by change 0 < scales.ratio; linarith) prepared.densityIdentity
    path.evolution globalInside inside (fun current member => (path.safe current member).le) receiver distancePositive
    (small _ secondPhysical) actualGeometry.2.2.2.2.1 alternativeArea (ratio _ secondPhysical)
  rw [prepared.referenceIdentity, firstEquation, secondEquation]
  abel

end EulerNonuniqueness.Paper
