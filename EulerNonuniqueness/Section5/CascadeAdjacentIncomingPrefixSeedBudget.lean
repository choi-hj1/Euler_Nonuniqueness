import EulerNonuniqueness.Section5.CascadeIncomingSingletonArbitraryWeightForcing
import EulerNonuniqueness.Section5.CascadeStatement

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem adjacent_full_prefix_prefactor (scales : Scales) (index : ℕ)
    {coefficient : ℝ} (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (coefficientPositive : 0 < coefficient) :
    2 * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
        (coefficient * scales.omega (index + 1) * |scales.location index - scales.location (index + 1)| ^ 4) *
        (1 + scales.location index / scales.location (index + 1)) ≤
      (100 / coefficient) * (scales.seed index / scales.ratio ^ 2) := by
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have locationPositive := scales.location_pos (index + 1)
  have omegaNext : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ]
    ring
  have locationRatio : scales.location index / scales.location (index + 1) = 2 := by
    rw [scales.location_eq_inv_pow, scales.location_eq_inv_pow, pow_succ]
    field_simp
  rw [locationRatio, scales.adjacent_location_distance]
  norm_num only [show (1 : ℝ) + 2 = 3 by norm_num]
  have normalization :
      2 * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
          (coefficient * scales.omega (index + 1) * scales.location (index + 1) ^ 4) * 3 =
        ((6 * Real.pi * Real.sqrt 2 / Real.sqrt 3) / coefficient) * (scales.seed index / scales.ratio ^ 2) := by
    simp only [Scales.seed, scales.adjacent_location_distance, Scales.circulation, omegaNext]
    field_simp [coefficientPositive.ne', ratioPositive.ne', omegaPositive.ne', locationPositive.ne',
      Real.pi_ne_zero, (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne',
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
    ring
  have sqrtTwo : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtThree : (1 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have numeric : 6 * Real.pi * Real.sqrt 2 / Real.sqrt 3 ≤ (100 : ℝ) := by
    have product := mul_le_mul (mul_le_mul_of_nonneg_left Real.pi_lt_four.le (by norm_num : (0 : ℝ) ≤ 6))
      sqrtTwo (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 6 * 4)
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mpr
    nlinarith only [product, sqrtThree]
  have seedNonnegative : 0 ≤ scales.seed index := by
    dsimp only [Scales.seed]
    positivity
  rw [normalization]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right numeric coefficientPositive.le)
    (div_nonneg seedNonnegative (sq_nonneg scales.ratio))

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem exists_uniform_actual_adjacent_incoming_prefix_seed_budget :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ), ∀ extent ≥ (1 : ℝ),
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
    ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ terminal coefficient magnitude weight : ℝ,
    0 ≤ terminal → terminal ≤ path.stop → 0 < coefficient → 0 ≤ magnitude → 0 ≤ weight →
    (∀ time ∈ Icc 0 terminal, ∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    (∀ time ∈ Icc 0 terminal, ∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let length := changed.length (source.val + 1)
    let sourceRate := coefficient * changed.omega (source.val + 1)
    let state := fun time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed first second source time‖ +
      ‖quadrupoleCenter first time source - quadrupoleCenter second time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let forcing := prepared.selectedForeignForcing {source} receiver
    let observation := fun time => ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖ +
      ∑ patch : Fin 4, ‖patchCentroid first time receiver patch - patchCentroid second time receiver patch‖
    2 * weight ≤ sourceRate →
    (∀ time ∈ Icc 0 terminal, state time ≤ magnitude * Real.exp (sourceRate * (time - terminal))) →
    ContinuousOn forcing (Icc 0 terminal) ∧ ContinuousOn observation (Icc 0 terminal) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 terminal ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * observation time) volume 0 terminal ∧
    (∫ time in (0 : ℝ)..terminal, Real.exp (-weight * time) * forcing time) ≤
      (100 * constant / coefficient) * extent ^ 2 * (changed.seed (receiver.val + 1) / changed.ratio ^ 2) *
          magnitude * Real.exp (-weight * terminal) +
        constant * extent ^ 2 * changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5 *
          ∫ time in (0 : ℝ)..terminal, Real.exp (-weight * time) * observation time := by
  obtain ⟨rawCap, capPositive, constant, constantNonnegative, factory⟩ :=
    exists_uniform_actual_incoming_singleton_arbitrary_weight_forcing
  refine ⟨rawCap, capPositive, constant, constantNonnegative, ?_⟩
  intro extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [factory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_gt_atTop (0 : ℝ)] with frequency estimates frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent terminal coefficient magnitude weight
    terminalNonnegative terminalBound coefficientPositive magnitudeNonnegative weightNonnegative referenceExtent alternativeExtent
  dsimp only
  intro rateSeparated profile
  let changed : Scales := {scales with frequency := frequency}
  have ordered : receiver.val < source.val := by omega
  have data := estimates count phase dipoleAngle prepared path receiver source ordered terminal coefficient magnitude weight
    terminalNonnegative terminalBound coefficientPositive magnitudeNonnegative weightNonnegative referenceExtent alternativeExtent rateSeparated profile
  have full := data.2.2 terminal ⟨terminalNonnegative, le_rfl⟩
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at full
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have prefactor := adjacent_full_prefix_prefactor changed (receiver.val + 1) frequencyPositive ratioPositive coefficientPositive
  have adjacentIndex : source.val + 1 = (receiver.val + 1) + 1 := by omega
  simp only [← adjacentIndex] at prefactor
  have scaled := mul_le_mul_of_nonneg_left prefactor
    (show 0 ≤ constant * extent ^ 2 * magnitude * Real.exp (-weight * terminal) by positivity)
  have sourceBound : (2 * constant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 /
      (coefficient * changed.omega (source.val + 1) * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ^ 4) *
      (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * magnitude) * Real.exp (-weight * terminal) ≤
      (100 * constant / coefficient) * extent ^ 2 * (changed.seed (receiver.val + 1) / changed.ratio ^ 2) *
        magnitude * Real.exp (-weight * terminal) := by
    convert scaled using 1 <;> ring
  exact ⟨data.1, data.2.1, full.1, full.2.1, full.2.2.trans (add_le_add_right sourceBound _)⟩

end EulerNonuniqueness.Paper
