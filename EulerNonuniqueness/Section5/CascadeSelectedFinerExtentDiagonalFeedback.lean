import EulerNonuniqueness.Section5.CascadeSelectedFinerExtentForcingRow
import EulerNonuniqueness.Section1.SharpReceiverCorrectionRow

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem CascadeSourcePreparedPair.receiver_observation_le_five_location_macroSourceState
    {rawCap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ}
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin count) :
    ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time receiver -
        quadrupoleCenter prepared.reference time receiver‖ +
      (∑ patch : Fin 4, ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch -
        patchCentroid prepared.reference time receiver patch‖) ≤
      5 * scales.location (receiver.val + 1) * prepared.macroSourceState time receiver := by
  let first := prepared.referenceWitness.trajectory.movingFamily
  let second := prepared.trajectory.movingFamily
  let firstCenter := quadrupoleCenter first.patchMotion time receiver
  let secondCenter := quadrupoleCenter second.patchMotion time receiver
  let center := ‖firstCenter - secondCenter‖
  let relative := fun patch : Fin 4 =>
    ‖(first.cascadeCenters time (receiver, patch) - firstCenter) -
      (second.cascadeCenters time (receiver, patch) - secondCenter)‖
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have firstIdentity (patch : Fin 4) : first.cascadeCenters time (receiver, patch) =
      patchCentroid first.patchMotion time receiver patch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver patch
  have secondIdentity (patch : Fin 4) : second.cascadeCenters time (receiver, patch) =
      patchCentroid second.patchMotion time receiver patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver patch
  have individual (patch : Fin 4) :
      ‖patchCentroid first.patchMotion time receiver patch - patchCentroid second.patchMotion time receiver patch‖ ≤
        center + relative patch := by
    rw [← firstIdentity, ← secondIdentity]
    have triangle := norm_add_le (firstCenter - secondCenter)
      ((first.cascadeCenters time (receiver, patch) - firstCenter) -
        (second.cascadeCenters time (receiver, patch) - secondCenter))
    convert triangle using 1
    congr 1
    abel
  have finite := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => individual patch)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at finite
  norm_num only [Nat.cast_ofNat] at finite
  have relativeNonnegative : 0 ≤ ∑ patch : Fin 4, relative patch :=
    Finset.sum_nonneg (fun patch _ => norm_nonneg _)
  have geometric : center + (∑ patch : Fin 4,
      ‖patchCentroid first.patchMotion time receiver patch - patchCentroid second.patchMotion time receiver patch‖) ≤
      5 * (center + ∑ patch : Fin 4, relative patch) := by linarith only [finite, relativeNonnegative]
  have macroBound : center + (∑ patch : Fin 4, relative patch) ≤
      scales.location (receiver.val + 1) * prepared.macroSourceState time receiver := by
    have locationPositive := scales.location_pos (receiver.val + 1)
    dsimp only [CascadeSourcePreparedPair.macroSourceState]
    rw [mul_add, mul_div_cancel₀ _ locationPositive.ne']
    apply le_add_of_nonneg_right
    apply mul_nonneg locationPositive.le
    exact Finset.sum_nonneg (fun patch _ => add_nonneg (norm_nonneg _)
      (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)))
  have result := geometric.trans (mul_le_mul_of_nonneg_left macroBound (by norm_num : (0 : ℝ) ≤ 5))
  have centerReverse : ‖secondCenter - firstCenter‖ = center := norm_sub_rev _ _
  have patchReverse (patch : Fin 4) :
      ‖patchCentroid second.patchMotion time receiver patch - patchCentroid first.patchMotion time receiver patch‖ =
        ‖patchCentroid first.patchMotion time receiver patch - patchCentroid second.patchMotion time receiver patch‖ := norm_sub_rev _ _
  rw [prepared.referenceIdentity]
  change ‖secondCenter - firstCenter‖ + (∑ patch : Fin 4,
    ‖patchCentroid second.patchMotion time receiver patch - patchCentroid first.patchMotion time receiver patch‖) ≤ _
  simpa only [centerReverse, patchReverse, mul_assoc] using result

theorem exists_uniform_actual_selected_finer_extent_diagonal_feedback :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ), ∀ extent : ℝ, 1 ≤ extent →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 100 → ∀ tolerance > (0 : ℝ),
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count, ∀ selected : Finset (Fin count),
    (∀ source ∈ selected, receiver.val < source.val) →
    (∀ source ∈ selected, ∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    (∀ source ∈ selected, ∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let gap := fun source : Fin count => |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let state := fun source : Fin count => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed first second source time‖ +
      ‖quadrupoleCenter first time source - quadrupoleCenter second time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let sourceBudget := ∑ source ∈ selected,
      changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
        (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * state source
    0 ≤ prepared.selectedForeignForcing selected receiver time ∧
      prepared.selectedForeignForcing selected receiver time ≤
        constant * extent ^ 2 * sourceBudget + tolerance * prepared.macroSourceState time receiver := by
  obtain ⟨rawCap, capPositive, constant, constantNonnegative, factory⟩ :=
    exists_uniform_actual_selected_finer_extent_forcing_row
  refine ⟨rawCap, capPositive, constant, constantNonnegative, ?_⟩
  intro extent extentOne scales amplitudePositive ratioTwo alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall tolerance tolerancePositive
  filter_upwards [factory extent extentOne scales amplitudePositive ratioTwo alphaPositive orbit sectionTime
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_sharp_receiver_correction_row_small ratioTwo alphaPositive
      (constant := 5 * constant) (extent := extent) (by positivity) tolerancePositive,
    eventually_gt_atTop (0 : ℝ)]
    with frequency estimates correctionSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver selected ordered referenceExtent alternativeExtent
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let gap := fun source : Fin count => |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let state := fun source : Fin count => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference source time‖ +
    ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source - quadrupoleCenter prepared.reference time source‖ /
      changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let sourceBudget := ∑ source ∈ selected,
    changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
      (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * state source
  let coefficient := ∑ source ∈ selected,
    changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 5
  let observation := ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time receiver - quadrupoleCenter prepared.reference time receiver‖ +
    ∑ patch : Fin 4, ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch - patchCentroid prepared.reference time receiver patch‖
  have actual := estimates count phase dipoleAngle prepared path time inside receiver selected ordered referenceExtent alternativeExtent
  dsimp only at actual
  have literal : prepared.selectedForeignForcing selected receiver time ≤ constant * extent ^ 2 *
      (sourceBudget + coefficient * observation) := actual.2.2.2
  have different (source : Fin count) (member : source ∈ selected) : source ≠ receiver := by
    intro equality
    have strict := ordered source member
    rw [equality] at strict
    exact (lt_irrefl _ strict)
  have small := correctionSmall count receiver selected different
  change 5 * constant * extent ^ 2 * coefficient < tolerance at small
  have coefficientNonnegative : 0 ≤ coefficient := Finset.sum_nonneg fun source _ => div_nonneg
    (mul_nonneg (by
      have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioTwo]
      exact (changed.circulation_pos frequencyPositive ratioPositive _).le) (sq_nonneg _)) (pow_nonneg (abs_nonneg _) _)
  have macroNonnegative := prepared.macroSourceState_nonnegative time receiver
  have observerBound : observation ≤ 5 * prepared.macroSourceState time receiver := by
    have actualObserver := prepared.receiver_observation_le_five_location_macroSourceState path inside receiver
    have locationBound : 5 * changed.location (receiver.val + 1) ≤ 5 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (changed.location_le_one (receiver.val + 1)) (by norm_num : (0 : ℝ) ≤ 5)
    exact actualObserver.trans (mul_le_mul_of_nonneg_right locationBound macroNonnegative)
  have feedback : constant * extent ^ 2 * (coefficient * observation) ≤ tolerance * prepared.macroSourceState time receiver := by
    have observed := mul_le_mul_of_nonneg_left observerBound
      (mul_nonneg (mul_nonneg constantNonnegative (sq_nonneg extent)) coefficientNonnegative)
    have smallScaled := mul_le_mul_of_nonneg_right small.le macroNonnegative
    calc
      _ ≤ (5 * constant * extent ^ 2 * coefficient) * prepared.macroSourceState time receiver := by
        convert observed using 1 <;> ring
      _ ≤ _ := smallScaled
  refine ⟨actual.2.2.1, ?_⟩
  change prepared.selectedForeignForcing selected receiver time ≤
    constant * extent ^ 2 * sourceBudget + tolerance * prepared.macroSourceState time receiver
  calc
    _ ≤ constant * extent ^ 2 * (sourceBudget + coefficient * observation) := literal
    _ = constant * extent ^ 2 * sourceBudget + constant * extent ^ 2 * (coefficient * observation) := mul_add _ _ _
    _ ≤ _ := add_le_add_left feedback _

end EulerNonuniqueness.Paper
