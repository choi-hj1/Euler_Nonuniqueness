import EulerNonuniqueness.Section6.SourcePacketReferenceBlockCenterBudget
import EulerNonuniqueness.Section6.SourcePacketReferenceProjectionBound
import EulerNonuniqueness.Section6.SourcePacketReferenceRecipient
import EulerNonuniqueness.Section6.SourcePacketPhysicalComparison

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def referenceBlockSourceInput {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (receiver source : Fin count) (time : ℝ) : ℝ :=
  let strain := vorticityComplexStrain (quadrupoleDensity scales motion time source) (quadrupoleCenter motion time receiver)
  (pointShapeForcing (positiveHalfDiagonal motion time receiver) (negativeHalfDiagonal motion time receiver)
    (strain * star (positiveHalfDiagonal motion time receiver))
    (strain * star (negativeHalfDiagonal motion time receiver))).1

theorem exists_reference_block_source_input_frozen_budget :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 0 < scales.alpha →
    ∀ tolerance > (0 : ℝ), max 2 (16384 / tolerance) ≤ scales.ratio →
    ∀ constant ≥ (0 : ℝ), constant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ᶠ frequency : ℝ in atTop, ∀ {count : ℕ} {phase : Fin count → ℝ},
    ∀ witness : ReferenceMaterialCoarseWitness {scales with frequency := frequency} phase threshold constant,
    ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start horizon : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ 1 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := witness.trajectory.movingFamily.patchMotion
    let decay := 2 * Real.sqrt 2 * changed.omega source.val
    let frozenDistance := ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) *
      |referenceBlockSourceInput changed motion receiver source (start + elapsed)|) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      |referenceBlockSourceInput changed motion receiver source (start + elapsed)|) ≤
      tolerance * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * frozenDistance ^ 4)) := by
  obtain ⟨radius, radiusPositive, radiusSmall, recipient⟩ := exists_source_packet_reference_recipient
  obtain ⟨chartRadius, chartPositive, projection⟩ := exists_reference_strain_projection_bound
  refine ⟨radius, radiusPositive, radiusSmall, ?_⟩
  intro scales amplitudePositive alphaPositive tolerance tolerancePositive ratioLarge constant constantNonnegative amplitudeBound threshold thresholdBound
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioBudget : max 2 (8192 / (tolerance / 2)) ≤ scales.ratio := by
    convert ratioLarge using 1 <;> congr 1 <;> field_simp <;> ring
  filter_upwards [scales.eventually_reference_blockcenter_source_frozen_budget amplitudePositive alphaPositive
      (show 0 < tolerance / 2 by positivity) ratioBudget constantNonnegative,
    recipient scales amplitudePositive ratioBound alphaPositive constant constantNonnegative amplitudeBound threshold thresholdBound
      chartRadius 1 chartPositive (by norm_num)] with frequency budget chart
  intro count phase witness receiver source adjacent start horizon startNonnegative horizonNonnegative endBound
  let changed : Scales := {scales with frequency := frequency}
  let family := witness.trajectory.movingFamily
  let motion := family.patchMotion
  let decay := 2 * Real.sqrt 2 * changed.omega source.val
  let field := fun elapsed => vorticityComplexStrain (quadrupoleDensity changed motion (start + elapsed) source)
    (quadrupoleCenter motion (start + elapsed) receiver)
  let weighted := fun elapsed => Real.exp (-decay * elapsed) * ‖field elapsed‖
  let actual := fun elapsed => Real.exp (-decay * elapsed) *
    |referenceBlockSourceInput changed motion receiver source (start + elapsed)|
  have thresholdSmall : threshold ≤ 1 / 4 := (thresholdBound.trans radiusSmall).trans (by norm_num)
  obtain ⟨fieldIntegrable, fieldBound⟩ := budget witness thresholdSmall receiver source adjacent start horizon
    startNonnegative horizonNonnegative (by linarith)
  have timeInside (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : actual elapsed ≤ 5 * weighted elapsed := by
    have data := chart witness (start + elapsed) (timeInside elapsed inside) receiver
    have bound := projection _ _ (field elapsed) data.1 data.2.1 data.2.2.1
    have multiplied := mul_le_mul_of_nonneg_left bound (Real.exp_pos (-decay * elapsed)).le
    change Real.exp (-decay * elapsed) * |referenceBlockSourceInput changed motion receiver source (start + elapsed)| ≤ _ at multiplied
    convert multiplied using 1 <;> dsimp only [actual, weighted] <;> ring
  have shift : Measurable (fun elapsed : ℝ => start + elapsed) := measurable_const.add measurable_id
  have centerMeasurable := (family.quadrupoleCenter_continuous receiver).measurable
  have physical := family.measurable_quadrupole_strain_along changed witness.densityIdentity source centerMeasurable
  have strainMeasurable : Measurable field := physical.comp shift
  have positiveMeasurable : Measurable (fun elapsed => positiveHalfDiagonal motion (start + elapsed) receiver) :=
    (((family.patchCentroid_continuous receiver 0).sub (family.patchCentroid_continuous receiver 1)).div_const 2).measurable.comp shift
  have negativeMeasurable : Measurable (fun elapsed => negativeHalfDiagonal motion (start + elapsed) receiver) :=
    (((family.patchCentroid_continuous receiver 2).sub (family.patchCentroid_continuous receiver 3)).div_const 2).measurable.comp shift
  have inputMeasurable := measurable_pointShapeForcing_first positiveMeasurable negativeMeasurable
    (strainMeasurable.mul (measurable_complex_star positiveMeasurable))
    (strainMeasurable.mul (measurable_complex_star negativeMeasurable))
  have actualMeasurable : Measurable actual :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul inputMeasurable.abs
  have majorant : IntervalIntegrable (fun elapsed => 5 * weighted elapsed) volume 0 horizon := fieldIntegrable.const_mul 5
  have actualIntegrable := majorant.mono_fun' actualMeasurable.aestronglyMeasurable.restrict (by
    rw [uIoc_of_le horizonNonnegative]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))]
    exact pointwise elapsed ⟨inside.1.le, inside.2⟩)
  refine ⟨actualIntegrable, ?_⟩
  have integrated := intervalIntegral.integral_mono_on horizonNonnegative actualIntegrable majorant pointwise
  rw [intervalIntegral.integral_const_mul] at integrated
  have seedNonnegative : 0 ≤ Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 *
        ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ ^ 4) := by positivity
  change 4 * (∫ elapsed in (0 : ℝ)..horizon, weighted elapsed) ≤ _ at fieldBound
  change (∫ elapsed in (0 : ℝ)..horizon, actual elapsed) ≤ _
  nlinarith

end EulerNonuniqueness.Paper
