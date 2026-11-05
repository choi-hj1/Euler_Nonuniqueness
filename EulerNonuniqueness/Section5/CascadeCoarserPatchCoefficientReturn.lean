import EulerNonuniqueness.Section5.CascadeCoarserPatchVirtualSeriesFeedback

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_coarser_patch_coefficient_return :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ {time : ℝ}, time ∈ Icc 0 path.stop → ∀ receiver : Fin count × Fin 4,
    ∀ radius : ℝ, 0 ≤ radius → radius ≤ scales.location (receiver.1.val + 1) / (100000 * 96) →
    let changed : Scales := {scales with frequency := frequency}
    let reference := prepared.referenceWitness.trajectory.movingFamily
    let alternative := prepared.trajectory.movingFamily
    let selected := Finset.univ.filter (fun source : Fin count => source.val < receiver.1.val)
    let term := fun (source : Fin count) (power : ℕ) => (96 : ℝ) ^ (power + 1) *
      ‖(alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid alternative.patchMotion current receiver.1 receiver.2)
          radius (power + 1) time -
        (reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid reference.patchMotion current receiver.1 receiver.2)
          radius (power + 1) time‖
    (∀ source ∈ selected, Summable (term source)) ∧
    (∑ source ∈ selected, ∑' power : ℕ, term source power) ≤
      (constant / changed.location (receiver.1.val + 1) ^ 4) *
        (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => if source.val ≤ receiver.1.val then
          changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖ := by
  obtain ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, constantNonnegative, factory⟩ :=
    exists_uniform_actual_coarser_patch_virtual_series_feedback
  refine ⟨rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [factory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall] with frequency estimates
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver radius radiusNonnegative radiusSmall
  obtain ⟨shapes, actual⟩ := estimates count phase dipoleAngle prepared path inside receiver
  have radiusBound : radius ≤ (1 / (100000 * 96)) * scales.location (receiver.1.val + 1) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using radiusSmall
  obtain ⟨firstReceiver, secondReceiver, summable, bound⟩ := actual radius radiusNonnegative radiusBound
  dsimp only at firstReceiver secondReceiver summable bound ⊢
  let original := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let comparison : MovingPatchFamilySourceComparison (count * 4) :=
    {original with receiverRadius := radius, receiverRadius_nonnegative := radiusNonnegative}
  let reference := prepared.referenceWitness.trajectory.movingFamily
  let alternative := prepared.trajectory.movingFamily
  have firstReceiverIdentity : comparison.firstReceiver time =
      patchCentroid reference.patchMotion time receiver.1 receiver.2 := firstReceiver
  have secondReceiverIdentity : comparison.secondReceiver time =
      patchCentroid alternative.patchMotion time receiver.1 receiver.2 := secondReceiver
  have termIdentity (source : Fin count) (power : ℕ) :
      (96 : ℝ) ^ (power + 1) *
        ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
            comparison.firstReceiver comparison.receiverRadius (power + 1) time -
          (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
            comparison.secondReceiver comparison.receiverRadius (power + 1) time‖ =
      (96 : ℝ) ^ (power + 1) *
        ‖(alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => patchCentroid alternative.patchMotion current receiver.1 receiver.2)
            radius (power + 1) time -
          (reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => patchCentroid reference.patchMotion current receiver.1 receiver.2)
            radius (power + 1) time‖ := by
    have firstFamily : (comparison.quadrupole source).first = reference.quadrupoleSubfamily source := by
      dsimp only [comparison, original, MovingPatchFamilySourceComparison.quadrupole,
        CascadeSourcePreparedPair.sourceComparison, reference]
    have secondFamily : (comparison.quadrupole source).second = alternative.quadrupoleSubfamily source := by
      dsimp only [comparison, original, MovingPatchFamilySourceComparison.quadrupole,
        CascadeSourcePreparedPair.sourceComparison, alternative]
    rw [firstFamily, secondFamily]
    change (96 : ℝ) ^ (power + 1) *
      ‖(reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          comparison.firstReceiver radius (power + 1) time -
        (alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          comparison.secondReceiver radius (power + 1) time‖ = _
    dsimp only [FiniteMovingPatchFamily.exteriorTaylorCoefficient]
    rw [firstReceiverIdentity, secondReceiverIdentity, norm_sub_rev]
  refine ⟨?_, ?_⟩
  · intro source member
    have sourceSummable := summable source member
    change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
          comparison.firstReceiver comparison.receiverRadius (power + 1) time -
        (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
          comparison.secondReceiver comparison.receiverRadius (power + 1) time‖) at sourceSummable
    simpa only [termIdentity] using sourceSummable
  · change (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.1.val),
      ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
            comparison.firstReceiver comparison.receiverRadius (power + 1) time -
          (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
            comparison.secondReceiver comparison.receiverRadius (power + 1) time‖) ≤ _ at bound
    simpa only [termIdentity] using bound

end EulerNonuniqueness.Paper
