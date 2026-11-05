import EulerNonuniqueness.Section5.CascadeSourcePreparedPair
import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry
import EulerNonuniqueness.Section3.DiskSpectralSourceRadius
import EulerNonuniqueness.Section3.MovingCentroidGaugeArea

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

structure ActualMaterialSpectralShape (sourceRadius : ℝ) (data : PeriodicC1HolderHalf) : Prop where
  small : ‖diskPhysicalSpectralCoordinate data‖ < sourceRadius
  reconstruct : diskStationaryChart (diskSpectralTubularChart (diskPhysicalSpectralCoordinate data)) = data
  area : contourAreaFunctional data = Real.pi
  centroid : contourCentroidFunctional data = 0
  continuousVector : data ∈ contourContinuousVectorSubmodule
  stateContinuousVector : diskPhysicalSpectralCoordinate data ∈ contourContinuousVectorSubmodule

theorem CascadeSourcePreparedPair.raw_shape_caps
    {requestedCap : ℝ} (requestedPositive : 0 < requestedCap)
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeSourcePreparedPair requestedCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (label : Fin (count * 4)) :
    ‖(prepared.referenceWitness.trajectory.curve time).2.2 label - standardCircleBanach‖ < requestedCap ∧
    ‖(prepared.trajectory.curve time).2.2 label - standardCircleBanach‖ < requestedCap := by
  refine ⟨prepared.referenceShapeCap time ⟨inside.1, by linarith [inside.2, path.stopBound]⟩ label, ?_⟩
  have half : monitor / 2 < requestedCap := by linarith [prepared.monitorCap]
  exact ((path.shapeBound time inside label).trans_le (min_le_left _ _)).trans half

theorem exists_actual_source_stopped_shape_radius {sourceRadius : ℝ} (sourcePositive : 0 < sourceRadius) :
    ∃ rawCap > 0,
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
      (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
      (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair),
    ∀ time ∈ Icc 0 path.stop, ∀ label : Fin (count * 4),
      ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label) := by
  obtain ⟨rawCap, rawPositive, valid⟩ := diskPhysicalSpectralCoordinate_exists_source_radius sourcePositive
  refine ⟨rawCap, rawPositive, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant
    count prepared path time inside label
  have caps := prepared.raw_shape_caps rawPositive path inside label
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have pathInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have referenceContinuous := prepared.referenceWitness.continuousVectors time referenceInside label
  have alternativeContinuous := prepared.continuousVectors time ⟨inside.1, by linarith [inside.2, path.stopBound]⟩ label
  have referenceValid := valid _ caps.1
  have alternativeValid := valid _ caps.2
  have referenceArea := prepared.referenceWitness.trajectory.shape_area_eq_pi_of_margin (fun _ => rfl)
    prepared.referenceWitness.marginPositive referenceInside (by norm_num) prepared.referenceWitness.safe label
  have alternativeArea := prepared.trajectory.shape_area_eq_pi_of_margin (fun _ => rfl)
    prepared.marginPositive inside (by linarith [path.stopBound]) (fun current member => (path.safe current member).le) label
  have referenceCentroid := prepared.referenceWitness.trajectory.contourCentroid_conserved pathInside label
  have alternativeCentroid := prepared.trajectory.contourCentroid_conserved pathInside label
  refine ⟨{
    small := referenceValid.1
    reconstruct := referenceValid.2.1
    area := referenceArea
    centroid := referenceCentroid.trans contourCentroidFunctional_standardCircle_zero
    continuousVector := referenceContinuous
    stateContinuousVector := referenceValid.2.2.2 referenceContinuous
  }, {
    small := alternativeValid.1
    reconstruct := alternativeValid.2.1
    area := alternativeArea
    centroid := alternativeCentroid.trans contourCentroidFunctional_standardCircle_zero
    continuousVector := alternativeContinuous
    stateContinuousVector := alternativeValid.2.2.2 alternativeContinuous
  }⟩

end EulerNonuniqueness.Paper
