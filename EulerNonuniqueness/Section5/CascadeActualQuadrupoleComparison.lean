import EulerNonuniqueness.Section5.CascadeActualSourceComparison
import EulerNonuniqueness.Section6.MovingPatchFamilyQuadrupole
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing
import EulerNonuniqueness.Section6.FourPointInversePowerRelative

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.CascadeSourcePreparedPair

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

variable {rawCap sourceRadius : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
  {count : ℕ}

theorem sourceComparison_quadrupole_masses
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (source : Fin count) (patch : Fin 4) :
    ((prepared.sourceComparison path inside receiver shapes).quadrupole source).first.density patch *
      volume.real ((((prepared.sourceComparison path inside receiver shapes).quadrupole source).first.patch patch).domain time) =
        scales.circulation (source.val + 1) * Section6.fourPointSign patch := by
  let comparison := prepared.sourceComparison path inside receiver shapes
  change comparison.first.density (finProdFinEquiv (source, patch)) *
    volume.real ((comparison.first.patch (finProdFinEquiv (source, patch))).domain comparison.time) = _
  rw [comparison.firstArea]
  change prepared.referenceWitness.configuration.density (finProdFinEquiv (source, patch)) *
    (Real.pi * prepared.referenceWitness.configuration.radius (finProdFinEquiv (source, patch)) ^ 2) = _
  rw [prepared.referenceWitness.densityIdentity, prepared.referenceWitness.radiusIdentity]
  calc
    _ = (Real.pi * scales.radius (source.val + 1) ^ 2 * scales.amplitude * scales.omega (source.val + 1) ^ 4) *
        patchSign patch := by ring
    _ = _ := by rw [scales.patch_circulation amplitudePositive frequencyPositive ratioPositive]; rfl

theorem sourceComparison_first_true_centers
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (source : Fin (count * 4)) :
    ((prepared.sourceComparison path inside receiver shapes).first.patch source).center time =
      ((prepared.sourceComparison path inside receiver shapes).first.patch source).centroid time := by
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  exact (prepared.referenceWitness.trajectory.movingPatch_centroid_eq_center_of_initial_circles
    (fun _ => rfl) globalInside source).symm

theorem sourceComparison_quadrupole_first_signed_moment
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (source : Fin count) (center : ℂ) :
    Section6.fourPointSignedMoment (fun patch =>
      ((((prepared.sourceComparison path inside receiver shapes).quadrupole source).first.patch patch).center time - center)) =
        4 * centroidAsymmetry prepared.referenceWitness.trajectory.movingFamily.patchMotion time source := by
  rw [Section6.fourPointSignedMoment_centered]
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  change Section6.fourPointSignedMoment (fun patch => prepared.referenceWitness.trajectory.movingFamily.cascadeCenters time (source, patch)) = _
  simp_rw [prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
  exact centroid_fourPointSignedMoment _ _ _

theorem sourceComparison_quadrupole_second_signed_moment
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (source : Fin count) (center : ℂ) :
    Section6.fourPointSignedMoment (fun patch =>
      ((((prepared.sourceComparison path inside receiver shapes).quadrupole source).second.patch patch).center time - center)) =
        4 * centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time source := by
  rw [Section6.fourPointSignedMoment_centered]
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  change Section6.fourPointSignedMoment (fun patch => prepared.trajectory.movingFamily.cascadeCenters time (source, patch)) = _
  simp_rw [prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
  exact centroid_fourPointSignedMoment _ _ _

end EulerNonuniqueness.Paper.CascadeSourcePreparedPair
