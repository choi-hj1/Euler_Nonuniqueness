import EulerNonuniqueness.Section5.CascadeSelectedFinerExtentDiagonalFeedback

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem incoming_singleton_normalization
    {receiver source distance mass state macroState observation constant extent : ℝ}
    (receiverPositive : 0 < receiver) (sourcePositive : 0 < source) (distancePositive : 0 < distance)
    (receiverOne : receiver ≤ 1) (sourceBelow : source ≤ receiver) (receiverGap : receiver ≤ 2 * distance)
    (massNonnegative : 0 ≤ mass) (stateNonnegative : 0 ≤ state) (macroNonnegative : 0 ≤ macroState)
    (constantNonnegative : 0 ≤ constant) (observed : observation ≤ 5 * receiver * macroState) :
    receiver ^ 4 * (constant * extent ^ 2 *
        (mass / distance ^ 4 * (1 + receiver / source) * state + mass / distance ^ 5 * observation)) ≤
      (160 * constant) * extent ^ 2 * mass * (1 + source⁻¹) * state +
        ((160 * constant) * extent ^ 2 * mass / source ^ 4) * (receiver ^ 4 * macroState) := by
  have fourth : receiver ^ 4 / distance ^ 4 ≤ 16 := by
    apply (div_le_iff₀ (pow_pos distancePositive 4)).mpr
    have actual := pow_le_pow_left₀ receiverPositive.le receiverGap 4
    nlinarith only [actual]
  have ratio : 1 + receiver / source ≤ 1 + source⁻¹ := by
    have actual := div_le_div_of_nonneg_right receiverOne sourcePositive.le
    simpa only [one_div] using add_le_add_left actual 1
  have sourceBound : receiver ^ 4 * (mass / distance ^ 4 * (1 + receiver / source) * state) ≤
      16 * mass * (1 + source⁻¹) * state := by
    calc
      _ = (receiver ^ 4 / distance ^ 4) * mass * (1 + receiver / source) * state := by ring
      _ ≤ 16 * mass * (1 + source⁻¹) * state := by gcongr
  have fifth : receiver ^ 5 ≤ 32 * distance ^ 5 := by
    have actual := pow_le_pow_left₀ receiverPositive.le receiverGap 5
    nlinarith only [actual]
  have sourceFourth := pow_le_pow_left₀ sourcePositive.le sourceBelow 4
  have numerator : 5 * receiver * source ^ 4 ≤ 160 * distance ^ 5 := by
    have actual := mul_le_mul_of_nonneg_left sourceFourth receiverPositive.le
    nlinarith only [actual, fifth]
  have coefficient : 5 * receiver / distance ^ 5 ≤ 160 / source ^ 4 :=
    (div_le_div_iff₀ (pow_pos distancePositive 5) (pow_pos sourcePositive 4)).mpr (by nlinarith only [numerator])
  have correctionBound : receiver ^ 4 * (mass / distance ^ 5 * observation) ≤
      160 * mass / source ^ 4 * (receiver ^ 4 * macroState) := by
    calc
      _ ≤ receiver ^ 4 * (mass / distance ^ 5 * (5 * receiver * macroState)) := by gcongr
      _ = (5 * receiver / distance ^ 5) * mass * (receiver ^ 4 * macroState) := by ring
      _ ≤ (160 / source ^ 4) * mass * (receiver ^ 4 * macroState) := by gcongr
      _ = _ := by ring
  have combined := mul_le_mul_of_nonneg_left (add_le_add sourceBound correctionBound)
    (mul_nonneg constantNonnegative (sq_nonneg extent))
  have sourceNonnegative : 0 ≤ mass * (1 + source⁻¹) * state := by positivity
  have enlarged : 16 * mass * (1 + source⁻¹) * state ≤ 160 * mass * (1 + source⁻¹) * state := by
    nlinarith only [sourceNonnegative]
  have final := combined.trans (mul_le_mul_of_nonneg_left (add_le_add_right enlarged _)
    (mul_nonneg constantNonnegative (sq_nonneg extent)))
  convert final using 1 <;> ring

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_incoming_singleton_common_envelope :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ), ∀ extent : ℝ, 1 ≤ extent →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 100 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ receiver source : Fin count, receiver.val < source.val →
    (∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    (∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let state := prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed first second source time‖ +
      ‖quadrupoleCenter first time source - quadrupoleCenter second time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    changed.location (receiver.val + 1) ^ 4 * prepared.selectedForeignForcing {source} receiver time ≤
      constant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
          (1 + (changed.location (source.val + 1))⁻¹) * state +
        (constant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 /
          changed.location (source.val + 1) ^ 4) *
            (changed.location (receiver.val + 1) ^ 4 * prepared.macroSourceState time receiver) := by
  obtain ⟨rawCap, capPositive, constant, constantNonnegative, factory⟩ :=
    exists_uniform_actual_selected_finer_extent_forcing_row
  refine ⟨rawCap, capPositive, 160 * constant, by positivity, ?_⟩
  intro extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [factory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_gt_atTop (0 : ℝ)] with frequency estimates frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver source ordered referenceExtent alternativeExtent
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let receiverLocation := changed.location (receiver.val + 1)
  let sourceLocation := changed.location (source.val + 1)
  let distance := |receiverLocation - sourceLocation|
  let mass := changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2
  let state := prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed first second source time‖ +
    ‖quadrupoleCenter first time source - quadrupoleCenter second time source‖ / sourceLocation +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let observation := ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖ +
    ∑ patch : Fin 4, ‖patchCentroid first time receiver patch - patchCentroid second time receiver patch‖
  have actual := (estimates count phase dipoleAngle prepared path time inside receiver {source}
    (by intro current member; rcases Finset.mem_singleton.mp member with rfl; exact ordered)
    (by intro current member; rcases Finset.mem_singleton.mp member with rfl; exact referenceExtent)
    (by intro current member; rcases Finset.mem_singleton.mp member with rfl; exact alternativeExtent)).2.2.2
  dsimp only at actual
  simp only [Finset.sum_singleton] at actual
  have literal : prepared.selectedForeignForcing {source} receiver time ≤ constant * extent ^ 2 *
      (mass / distance ^ 4 * (1 + receiverLocation / sourceLocation) * state + mass / distance ^ 5 * observation) := actual
  have receiverPositive : 0 < receiverLocation := changed.location_pos _
  have sourcePositive : 0 < sourceLocation := changed.location_pos _
  have sourceHalf : sourceLocation ≤ receiverLocation / 2 := changed.location_le_half_of_lt (show receiver.val + 1 < source.val + 1 by omega)
  have receiverGap : receiverLocation ≤ 2 * distance := by
    dsimp only [distance]
    rw [abs_of_nonneg (by linarith only [sourceHalf, receiverPositive])]
    linarith only [sourceHalf]
  have distancePositive : 0 < distance := by linarith only [receiverPositive, receiverGap]
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have massNonnegative : 0 ≤ mass := mul_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have centeredNonnegative : 0 ≤ prepared.rawSourceCenteredState time source := by
    unfold CascadeSourcePreparedPair.rawSourceCenteredState
    exact div_nonneg (norm_nonneg _) (changed.length_pos _).le
  have rawNonnegative (patch : Fin 4) : 0 ≤ prepared.rawSourceShapeBudget time source patch := by
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have stateNonnegative : 0 ≤ state := add_nonneg
    (add_nonneg (add_nonneg centeredNonnegative (norm_nonneg _)) (div_nonneg (norm_nonneg _) sourcePositive.le))
    (Finset.sum_nonneg (fun patch _ => rawNonnegative patch))
  have normalization := incoming_singleton_normalization (extent := extent) receiverPositive sourcePositive distancePositive
    (changed.location_le_one (receiver.val + 1)) (by linarith only [sourceHalf, receiverPositive]) receiverGap
    massNonnegative stateNonnegative (prepared.macroSourceState_nonnegative time receiver) constantNonnegative
    (prepared.receiver_observation_le_five_location_macroSourceState path inside receiver)
  have scaled := mul_le_mul_of_nonneg_left literal (pow_nonneg receiverPositive.le 4)
  exact (scaled.trans normalization).trans_eq (by dsimp only [mass]; ring)

end EulerNonuniqueness.Paper
