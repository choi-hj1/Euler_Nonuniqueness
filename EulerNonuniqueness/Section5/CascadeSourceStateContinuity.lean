import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

open FiniteMovingPatchFamily

theorem exists_uniform_actual_source_state_continuity :
    ∃ rawCap > (0 : ℝ),
    ∀ {requestedCap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
      {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair requestedCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    0 < requestedCap → requestedCap ≤ rawCap →
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ source : Fin count,
    (∀ patch : Fin 4, ContinuousOn (fun time => prepared.rawSourceShapeBudget time source patch) (Icc 0 path.stop)) ∧
      ContinuousOn (fun time => prepared.rawSourceCenteredState time source) (Icc 0 path.stop) ∧
      ContinuousOn (fun time =>
        ‖quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source -
          quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ / scales.location (source.val + 1))
        (Icc 0 path.stop) ∧
      ContinuousOn (fun time => prepared.macroSourceState time source) (Icc 0 path.stop) := by
  obtain ⟨rawCap, rawPositive, rawContinuity⟩ := exists_uniform_actual_raw_spectral_continuity
  refine ⟨rawCap, rawPositive, ?_⟩
  intro requestedCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor
    monitor boundaryConstant count prepared requestedPositive requestedSmall path source
  have rawContinuous (patch : Fin 4) :
      ContinuousOn (fun time => prepared.rawSourceShapeBudget time source patch) (Icc 0 path.stop) := by
    obtain ⟨first, final⟩ := rawContinuity prepared requestedPositive requestedSmall path (finProdFinEquiv (source, patch))
    have firstProjection : ContinuousOn (fun time => diskPhysicalTransverseProjection
        (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time))
        (Icc 0 path.stop) := diskPhysicalTransverseProjection.continuous.comp_continuousOn first
    have finalProjection : ContinuousOn (fun time => diskPhysicalTransverseProjection
        (prepared.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time))
        (Icc 0 path.stop) := diskPhysicalTransverseProjection.continuous.comp_continuousOn final
    have firstNeutral : ContinuousOn (fun time => diskNeutralCLM
        (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time))
        (Icc 0 path.stop) := diskNeutralCLM.continuous.comp_continuousOn first
    have finalNeutral : ContinuousOn (fun time => diskNeutralCLM
        (prepared.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time))
        (Icc 0 path.stop) := diskNeutralCLM.continuous.comp_continuousOn final
    unfold CascadeSourcePreparedPair.rawSourceShapeBudget
    with_reducible_and_instances
      exact (firstProjection.sub finalProjection).norm.add
        ((firstProjection.norm.add finalProjection.norm).mul (firstNeutral.sub finalNeutral).norm)
  let first := prepared.referenceWitness.trajectory.movingFamily
  let final := prepared.trajectory.movingFamily
  have centroidContinuous (family : FiniteMovingPatchFamily (count * 4))
      (interior : ∀ label, Icc (0 : ℝ) path.stop ⊆ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (patch : Fin 4) :
      ContinuousOn (fun time => patchCentroid family.patchMotion time source patch) (Icc 0 path.stop) := by
    simp_rw [FiniteMovingPatchFamily.patchCentroid_eq]
    exact fun time inside => ((family.patch _).centroid_contDiffAt (interior _ inside)).continuousAt.continuousWithinAt
  have firstInterior (label : Fin (count * 4)) :
      Icc (0 : ℝ) path.stop ⊆ Ioo (first.patch label).initialTime (first.patch label).finalTime := by
    intro time inside
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have finalInterior (label : Fin (count * 4)) :
      Icc (0 : ℝ) path.stop ⊆ Ioo (final.patch label).initialTime (final.patch label).finalTime := by
    intro time inside
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have firstCenter : ContinuousOn (fun time => quadrupoleCenter first.patchMotion time source) (Icc 0 path.stop) :=
    (continuousOn_finset_sum _ (fun patch _ => centroidContinuous first firstInterior patch)).div_const 4
  have finalCenter : ContinuousOn (fun time => quadrupoleCenter final.patchMotion time source) (Icc 0 path.stop) :=
    (continuousOn_finset_sum _ (fun patch _ => centroidContinuous final finalInterior patch)).div_const 4
  have centeredContinuous : ContinuousOn (fun time =>
      (fun patch => patchCentroid first.patchMotion time source patch - quadrupoleCenter first.patchMotion time source) -
      (fun patch => patchCentroid final.patchMotion time source patch - quadrupoleCenter final.patchMotion time source))
      (Icc 0 path.stop) :=
    continuousOn_pi.mpr fun patch =>
      ((centroidContinuous first firstInterior patch).sub firstCenter).sub
        ((centroidContinuous final finalInterior patch).sub finalCenter)
  refine ⟨rawContinuous, centeredContinuous.norm.div_const _, (firstCenter.sub finalCenter).norm.div_const _, ?_⟩
  have gaugeContinuous (family : FiniteMovingPatchFamily (count * 4)) (patch : Fin 4) :
      ContinuousOn (fun time => family.cascadeCenters time (source, patch)) (Icc 0 path.stop) :=
    fun time _ => ((family.patch _).center_equation time).continuousAt.continuousWithinAt
  have centeredSum := continuousOn_finset_sum Finset.univ (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) =>
    (((gaugeContinuous first patch).sub firstCenter).sub ((gaugeContinuous final patch).sub finalCenter)).norm)
  have rawSum := continuousOn_finset_sum Finset.univ (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => rawContinuous patch)
  have identity : (fun time => prepared.macroSourceState time source) = fun time =>
      (‖quadrupoleCenter first.patchMotion time source - quadrupoleCenter final.patchMotion time source‖ +
        ∑ patch : Fin 4, ‖(first.cascadeCenters time (source, patch) - quadrupoleCenter first.patchMotion time source) -
          (final.cascadeCenters time (source, patch) - quadrupoleCenter final.patchMotion time source)‖) /
        scales.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch := by
    funext time
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.macroSourceState, CascadeSourcePreparedPair.rawSourceShapeBudget,
        MovingCentroidGaugeTrajectory.spectralCoordinate, first, final]
  rw [identity]
  exact (((firstCenter.sub finalCenter).norm.add centeredSum).div_const _).add rawSum

end EulerNonuniqueness.Paper
