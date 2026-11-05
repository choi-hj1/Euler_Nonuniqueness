import EulerNonuniqueness.Section5.CascadeActualQuadrupoleComparison
import EulerNonuniqueness.Section6.PaperStrongFirstMomentIdentity

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.CascadeSourcePreparedPair

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

variable {rawCap sourceRadius : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
  {count : ℕ}

theorem sourceComparison_quadrupole_signed_moment_difference_norm
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (source : Fin count) (firstCenter secondCenter : ℂ) :
    ‖Section6.fourPointSignedMoment (fun patch =>
        (((prepared.sourceComparison path inside receiver shapes).quadrupole source).first.patch patch).center time - firstCenter) -
      Section6.fourPointSignedMoment (fun patch =>
        (((prepared.sourceComparison path inside receiver shapes).quadrupole source).second.patch patch).center time - secondCenter)‖ =
      (scales.length (source.val + 1) ^ 2 / scales.location (source.val + 1)) *
        ‖relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference source time‖ := by
  rw [prepared.sourceComparison_quadrupole_first_signed_moment path inside receiver shapes,
    prepared.sourceComparison_quadrupole_second_signed_moment path inside receiver shapes]
  have actual := fourPointSignedMoment_difference_norm_eq_strong_firstMoment scales
    prepared.referenceWitness.trajectory.movingFamily.patchMotion prepared.trajectory.movingFamily.patchMotion source time
    firstCenter secondCenter
  simp only [Section6.fourPointSignedMoment_centered, centroid_fourPointSignedMoment] at actual
  apply actual.trans
  apply congrArg (fun value : ℝ => (scales.length (source.val + 1) ^ 2 / scales.location (source.val + 1)) * value)
  rw [prepared.referenceIdentity]
  simp only [relativeNormalizedFirstMoment, norm_smul]
  rw [norm_sub_rev]

theorem sourceComparison_quadrupole_centered_difference_sum_le
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (source : Fin count) :
    (∑ patch : Fin 4,
      ‖((((prepared.sourceComparison path inside receiver shapes).quadrupole source).first.patch patch).center time -
          quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source) -
        ((((prepared.sourceComparison path inside receiver shapes).quadrupole source).second.patch patch).center time -
          quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source)‖) ≤
      4 * ‖(fun patch => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
          quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source) -
        (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
          quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source)‖ := by
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  change (∑ patch : Fin 4,
    ‖(prepared.referenceWitness.trajectory.movingFamily.cascadeCenters time (source, patch) -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source) -
      (prepared.trajectory.movingFamily.cascadeCenters time (source, patch) -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source)‖) ≤ _
  simp_rw [prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside,
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
  exact quadrupoleCenteredPositionDifference_sum_le_array_norm
    prepared.referenceWitness.trajectory.movingFamily.patchMotion prepared.trajectory.movingFamily.patchMotion source time

end EulerNonuniqueness.Paper.CascadeSourcePreparedPair
