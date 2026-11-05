import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.CascadeSourcePreparedPair

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

variable {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
  {count : ℕ}

theorem macroSourceState_le_centered_and_raw
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (source : Fin count) :
    prepared.macroSourceState time source ≤
      ‖quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ / scales.location (source.val + 1) +
      4 * (scales.length (source.val + 1) / scales.location (source.val + 1)) *
        prepared.rawSourceCenteredState time source +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch := by
  let first := prepared.referenceWitness.trajectory.movingFamily
  let final := prepared.trajectory.movingFamily
  let centered := (fun patch => patchCentroid first.patchMotion time source patch - quadrupoleCenter first.patchMotion time source) -
    (fun patch => patchCentroid final.patchMotion time source patch - quadrupoleCenter final.patchMotion time source)
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have positionSum : (∑ patch : Fin 4,
      ‖(first.cascadeCenters time (source, patch) - quadrupoleCenter first.patchMotion time source) -
        (final.cascadeCenters time (source, patch) - quadrupoleCenter final.patchMotion time source)‖) ≤ 4 * ‖centered‖ := by
    dsimp only [first, final]
    simp_rw [prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside,
      prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
    exact quadrupoleCenteredPositionDifference_sum_le_array_norm first.patchMotion final.patchMotion source time
  have normalized := div_le_div_of_nonneg_right positionSum (scales.location_pos (source.val + 1)).le
  have scaleIdentity : (4 * ‖centered‖) / scales.location (source.val + 1) =
      4 * (scales.length (source.val + 1) / scales.location (source.val + 1)) *
        prepared.rawSourceCenteredState time source := by
    dsimp only [rawSourceCenteredState, centered, first, final]
    field_simp [(scales.length_pos (source.val + 1)).ne', (scales.location_pos (source.val + 1)).ne']; ring
  rw [scaleIdentity] at normalized
  have identity : prepared.macroSourceState time source =
      ‖quadrupoleCenter first.patchMotion time source - quadrupoleCenter final.patchMotion time source‖ /
        scales.location (source.val + 1) +
      (∑ patch : Fin 4,
        ‖(first.cascadeCenters time (source, patch) - quadrupoleCenter first.patchMotion time source) -
          (final.cascadeCenters time (source, patch) - quadrupoleCenter final.patchMotion time source)‖) /
        scales.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch := by
    with_reducible_and_instances
      dsimp only [macroSourceState, rawSourceShapeBudget, MovingCentroidGaugeTrajectory.spectralCoordinate, first, final]
      rw [add_div]
  rw [identity]
  exact add_le_add_right (add_le_add_left normalized _) _

end EulerNonuniqueness.Paper.CascadeSourcePreparedPair
