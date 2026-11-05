import EulerNonuniqueness.Section6.SourcePacketAdjacentArbitraryWeightSeedBudget
import EulerNonuniqueness.Section5.CascadeOutgoingSingletonArbitraryWeightForcing

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem centroidAsymmetry_le_length_sq_add_relativeNormalizedFirstMoment
    {count : ℕ} (scales : Scales) (first second : PatchMotion count) (index : Fin count) (time : ℝ)
    (referenceNeutral : ‖centroidAsymmetry second time index‖ ≤ scales.length (index.val + 1) ^ 2) :
    ‖centroidAsymmetry first time index‖ ≤ scales.length (index.val + 1) ^ 2 +
      scales.length (index.val + 1) ^ 2 / (4 * scales.location (index.val + 1)) *
        ‖relativeNormalizedFirstMoment scales first second index time‖ := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have locationPositive := scales.location_pos (index.val + 1)
  have momentIdentity : ‖relativeNormalizedFirstMoment scales first second index time‖ =
      (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) *
        ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ := by
    rw [relativeNormalizedFirstMoment, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have differenceIdentity : ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ =
      scales.length (index.val + 1) ^ 2 / (4 * scales.location (index.val + 1)) *
        ‖relativeNormalizedFirstMoment scales first second index time‖ := by
    rw [momentIdentity]
    field_simp
    ring
  have triangle := norm_sub_le (centroidAsymmetry first time index - centroidAsymmetry second time index)
    (-centroidAsymmetry second time index)
  rw [sub_neg_eq_add, sub_add_cancel, norm_neg, differenceIdentity] at triangle
  linarith only [triangle, referenceNeutral]

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_actual_adjacent_outgoing_arbitrary_weight_forcing :
    ∃ thresholdRadius > (0 : ℝ), thresholdRadius ≤ 1 / 8 ∧ ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdRadius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {cap shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ receiver source : Fin count,
    receiver.val + 1 = source.val →
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    ‖firstDipoleSeparation first start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation first start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter first start source - secondDipoleCenter first start source)).re →
    ‖firstDipoleCenter first start source - secondDipoleCenter first start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    ∀ weight : ℝ, changed.omega (receiver.val + 1) ≤ weight →
    let forcing := prepared.selectedForeignForcing {source} receiver
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let seedCost := changed.seed (receiver.val + 1) *
      (1 + (1 + initialDistance + ‖relativeNormalizedFirstMoment changed first second source start‖) / changed.ratio)
    (∀ time ∈ Icc 0 path.stop,
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ∧
      Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source) ∧
      ∀ patch : Fin 4, Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source) ∧
        Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source) ∧
        Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source)) ∧
    ContinuousOn forcing (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 (start + horizon) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * forcing (start + elapsed)) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * forcing (start + elapsed)) ≤ constant * seedCost ∧
    (∫ time in (0 : ℝ)..start + horizon, Real.exp (-weight * time) * forcing time) ≤
      (∫ time in (0 : ℝ)..start, Real.exp (-weight * time) * forcing time) + Real.exp (-weight * start) * (constant * seedCost) := by
  obtain ⟨thresholdRadius, thresholdPositive, thresholdSmall, parentConstant, parentNonnegative, budgets⟩ :=
    exists_actual_outgoing_singleton_arbitrary_weight_forcing
  refine ⟨thresholdRadius, thresholdPositive, thresholdSmall, 128 * parentConstant, by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
    threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  filter_upwards [budgets scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative
      referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive
      (thresholdBound.trans thresholdSmall) referenceNonnegative, eventually_gt_atTop (0 : ℝ)]
    with frequency budgets mechanical frequencyPositive
  intro count phase dipoleAngle cap shapeRadius monitor prepared path receiver source adjacent
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper weight weightLarge
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have actualFrequencyPositive : 0 < changed.frequency := frequencyPositive
  have ordered : receiver.val < source.val := by omega
  obtain ⟨summable, forcingContinuous, originalIntegrable, elapsedIntegrable, elapsedBound, originalBound⟩ :=
    budgets count phase dipoleAngle prepared path receiver receiver source le_rfl ordered start horizon initialDistance
      startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
      firstInitial secondInitial initialProjection initialUpper weight weightLarge
  refine ⟨summable, forcingContinuous, originalIntegrable, elapsedIntegrable, ?_⟩
  have startInside : start ∈ Icc (0 : ℝ) 2 :=
    ⟨startNonnegative, by linarith only [horizonNonnegative, endBound, path.stopBound]⟩
  have referenceNeutral : ‖centroidAsymmetry second start source‖ ≤ changed.length (source.val + 1) ^ 2 :=
    (mechanical second prepared.referenceWitness.evolution prepared.referenceWitness.coarse start startInside source).2.2.2.1
  have neutralBound := centroidAsymmetry_le_length_sq_add_relativeNormalizedFirstMoment changed first second source start referenceNeutral
  have sourceIndex : source.val + 1 = (receiver.val + 1) + 1 := by omega
  have distanceIdentity : |changed.location (receiver.val + 1) - changed.location (source.val + 1)| =
      changed.location (source.val + 1) := by
    rw [sourceIndex, changed.adjacent_location_distance]
  have normalized := changed.adjacent_arbitrary_weight_cost_le_seed (receiver.val + 1) actualFrequencyPositive ratioPositive weightLarge
    (show 0 ≤ initialDistance by linarith only [initialLarge]) (norm_nonneg _)
    (by simpa only [← sourceIndex] using neutralBound)
  simp only [← sourceIndex] at normalized
  have costComparison : parentConstant *
      (changed.circulation (source.val + 1) ^ 2 /
          (weight ^ 2 * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ^ 4) +
        (1 + initialDistance) * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 /
          (weight * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ^ 4) +
        changed.circulation (source.val + 1) * ‖centroidAsymmetry first start source‖ /
          (weight * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ^ 3)) ≤
      (128 * parentConstant) * (changed.seed (receiver.val + 1) *
        (1 + (1 + initialDistance + ‖relativeNormalizedFirstMoment changed first second source start‖) / changed.ratio)) := by
    have scaled := mul_le_mul_of_nonneg_left normalized parentNonnegative
    rw [← distanceIdentity] at scaled
    simpa only [mul_assoc, mul_left_comm, mul_comm] using scaled
  exact ⟨elapsedBound.trans costComparison, originalBound.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left costComparison (Real.exp_pos _).le) _)⟩

end EulerNonuniqueness.Paper
