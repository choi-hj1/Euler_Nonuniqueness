import EulerNonuniqueness.Section5.CascadeExtentMacroSourceStateBound
import EulerNonuniqueness.Section4.QuadrupoleCenterNormBound

noncomputable section

open Set
open scoped BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_admissible_macro_source_bound :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ source : Fin count,
      scales.location (source.val + 1) * prepared.macroSourceState time source ≤ constant := by
  obtain ⟨rawCap, capPositive, rawConstant, rawNonnegative, _, shapes⟩ :=
    exists_uniform_actual_extent_macro_source_state_bound
  refine ⟨rawCap, capPositive, 72 + rawConstant, by linarith only [rawNonnegative], ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared path time inside source
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have centroidBound (side : Fin 2) (patch : Fin 4) :
      ‖patchCentroid (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time source patch‖ ≤ 4 := by
    fin_cases side
    · change ‖patchCentroid first time source patch‖ ≤ 4
      rw [← prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
      change ‖prepared.trajectory.center (finProdFinEquiv (source, patch)) time‖ ≤ 4
      rw [prepared.trajectory.center_eq_curve globalInside]
      exact (prepared.trajectory.admissible time).1 (finProdFinEquiv (source, patch))
    · change ‖patchCentroid prepared.reference time source patch‖ ≤ 4
      rw [prepared.referenceIdentity, ← prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
      change ‖prepared.referenceWitness.trajectory.center (finProdFinEquiv (source, patch)) time‖ ≤ 4
      rw [prepared.referenceWitness.trajectory.center_eq_curve globalInside]
      exact (prepared.referenceWitness.trajectory.admissible time).1 (finProdFinEquiv (source, patch))
  have firstCenter : ‖quadrupoleCenter first time source‖ ≤ 4 :=
    quadrupoleCenter_norm_le_of_patchCentroid_norm_le first time source (centroidBound 0)
  have secondCenter : ‖quadrupoleCenter second time source‖ ≤ 4 := by
    apply quadrupoleCenter_norm_le_of_patchCentroid_norm_le second time source
    intro patch
    have bound := centroidBound 1 patch
    change ‖patchCentroid prepared.reference time source patch‖ ≤ 4 at bound
    simpa only [prepared.referenceIdentity] using bound
  have centerDifference : ‖quadrupoleCenter second time source - quadrupoleCenter first time source‖ ≤ 8 :=
    (norm_sub_le _ _).trans (by linarith only [firstCenter, secondCenter])
  have centeredDifference (patch : Fin 4) :
      ‖(patchCentroid second time source patch - quadrupoleCenter second time source) -
        (patchCentroid first time source patch - quadrupoleCenter first time source)‖ ≤ 16 := by
    have firstPatch : ‖patchCentroid first time source patch‖ ≤ 4 := centroidBound 0 patch
    have secondPatch : ‖patchCentroid second time source patch‖ ≤ 4 := by
      have bound := centroidBound 1 patch
      change ‖patchCentroid prepared.reference time source patch‖ ≤ 4 at bound
      simpa only [prepared.referenceIdentity] using bound
    have secondOffset := norm_sub_le (patchCentroid second time source patch) (quadrupoleCenter second time source)
    have firstOffset := norm_sub_le (patchCentroid first time source patch) (quadrupoleCenter first time source)
    exact (norm_sub_le _ _).trans (by linarith only [secondOffset, firstOffset, firstPatch, secondPatch, firstCenter, secondCenter])
  have rawBound := (shapes 0 le_rfl prepared path time inside source).1
  have sumBound := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => centeredDifference patch)
  norm_num only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at sumBound
  have positive := scales.location_pos (source.val + 1)
  have macroEstimate : prepared.macroSourceState time source ≤ 72 / scales.location (source.val + 1) + rawConstant := by
    have identity : prepared.macroSourceState time source =
        (‖quadrupoleCenter second time source - quadrupoleCenter first time source‖ +
          ∑ patch : Fin 4,
            ‖(prepared.referenceWitness.trajectory.movingFamily.cascadeCenters time (source, patch) - quadrupoleCenter second time source) -
              (prepared.trajectory.movingFamily.cascadeCenters time (source, patch) - quadrupoleCenter first time source)‖) /
            scales.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch := by
      with_reducible_and_instances
        dsimp only [CascadeSourcePreparedPair.macroSourceState, CascadeSourcePreparedPair.rawSourceShapeBudget,
          MovingCentroidGaugeTrajectory.spectralCoordinate, first, second]
    rw [identity]
    simp_rw [prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside,
      prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
    have numerator : ‖quadrupoleCenter second time source - quadrupoleCenter first time source‖ +
        (∑ patch : Fin 4, ‖(patchCentroid second time source patch - quadrupoleCenter second time source) -
          (patchCentroid first time source patch - quadrupoleCenter first time source)‖) ≤ 72 := by linarith only [centerDifference, sumBound]
    have divided := div_le_div_of_nonneg_right numerator positive.le
    exact add_le_add divided rawBound
  have locationPositive := scales.location_pos (source.val + 1)
  have locationOne := scales.location_le_one (source.val + 1)
  calc
    _ ≤ scales.location (source.val + 1) *
        (72 / scales.location (source.val + 1) + rawConstant) :=
      mul_le_mul_of_nonneg_left macroEstimate locationPositive.le
    _ = 72 + scales.location (source.val + 1) * rawConstant := by field_simp; ring
    _ ≤ 72 + rawConstant := add_le_add_left (mul_le_of_le_one_left rawNonnegative locationOne) _

end EulerNonuniqueness.Paper
