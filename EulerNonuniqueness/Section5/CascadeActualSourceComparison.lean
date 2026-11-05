import EulerNonuniqueness.Section5.CascadeSourceShapeRadius
import EulerNonuniqueness.Section6.MovingPatchFamilyCenteredRelativeSeries

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.CascadeSourcePreparedPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

variable {rawCap sourceRadius : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
  {count : ℕ}

def sourceComparison
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label)) :
    MovingPatchFamilySourceComparison (count * 4) where
  first := prepared.referenceWitness.trajectory.movingFamily
  second := prepared.trajectory.movingFamily
  densityEqual := by
    intro label
    obtain ⟨pair, rfl⟩ := finProdFinEquiv.surjective label
    change prepared.referenceWitness.configuration.density (finProdFinEquiv pair) =
      prepared.configuration.density (finProdFinEquiv pair)
    rw [prepared.referenceWitness.densityIdentity pair.1 pair.2, prepared.densityIdentity pair.1 pair.2]
  firstReceiver := (prepared.referenceWitness.trajectory.movingFamily.patch receiver).center
  secondReceiver := (prepared.trajectory.movingFamily.patch receiver).center
  receiverRadius := (prepared.referenceWitness.trajectory.movingFamily.patch receiver).radius
  receiverRadius_nonnegative := (prepared.referenceWitness.trajectory.movingFamily.patch receiver).radius_positive.le
  time := time
  initial := fun label => diskPhysicalSpectralCoordinate ((prepared.referenceWitness.trajectory.curve time).2.2 label)
  final := fun label => diskPhysicalSpectralCoordinate ((prepared.trajectory.curve time).2.2 label)
  firstShape := by
    intro label
    exact (shapes label).1.reconstruct.symm
  secondShape := by
    intro label
    exact (shapes label).2.reconstruct.symm
  radiusEqual := by
    intro label
    obtain ⟨pair, rfl⟩ := finProdFinEquiv.surjective label
    change prepared.referenceWitness.configuration.radius (finProdFinEquiv pair) =
      prepared.configuration.radius (finProdFinEquiv pair)
    rw [prepared.referenceWitness.radiusIdentity pair.1 pair.2, prepared.radiusIdentity pair.1 pair.2]
  phaseEqual := by
    intro label
    obtain ⟨pair, rfl⟩ := finProdFinEquiv.surjective label
    exact (path.common_phase inside pair.1 pair.2).1
  firstArea := by
    intro label
    rw [(prepared.referenceWitness.trajectory.movingFamily.patch label).domain_area_eq_radius_sq_contourArea]
    change (prepared.referenceWitness.trajectory.movingFamily.patch label).radius ^ 2 *
      contourAreaFunctional ((prepared.referenceWitness.trajectory.curve time).2.2 label) = _
    rw [(shapes label).1.area]
    ring
  secondArea := by
    intro label
    rw [(prepared.trajectory.movingFamily.patch label).domain_area_eq_radius_sq_contourArea]
    change (prepared.trajectory.movingFamily.patch label).radius ^ 2 *
      contourAreaFunctional ((prepared.trajectory.curve time).2.2 label) = _
    rw [(shapes label).2.area]
    ring

theorem sourceComparison_states
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (label : Fin (count * 4)) :
    (prepared.sourceComparison path inside receiver shapes).initial label ∈ ball 0 sourceRadius ∧
    (prepared.sourceComparison path inside receiver shapes).final label ∈ ball 0 sourceRadius ∧
    contourCentroidFunctional (((prepared.sourceComparison path inside receiver shapes).first.patch label).shape time) = 0 ∧
    contourCentroidFunctional (((prepared.sourceComparison path inside receiver shapes).second.patch label).shape time) = 0 := by
  exact ⟨mem_ball_zero_iff.mpr (shapes label).1.small, mem_ball_zero_iff.mpr (shapes label).2.small,
    (shapes label).1.centroid, (shapes label).2.centroid⟩

end EulerNonuniqueness.Paper.CascadeSourcePreparedPair
