import EulerNonuniqueness.Section5.CascadeCoarserVelocityMacroFeedback
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section6.SourcePacketFinerPatchVelocitySeedTail
import EulerNonuniqueness.Section6.MovingPatchStrainMeasurability
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.Section6.LaplaceMomentErrorBound
import EulerNonuniqueness.General.ErasedAdjacentSum

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

open EulerNonuniqueness.General EulerNonuniqueness.Section6

theorem exists_uniform_actual_driven_patch_velocity_weighted_return :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    4 < scales.ratio ^ scales.alpha → ∀ {tolerance : ℝ}, 0 < tolerance →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver : Fin count × Fin 4, ∀ adjacent : Fin count, receiver.1.val + 1 = adjacent.val →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop → ∀ weight : ℝ, 0 < weight →
    let changed : Scales := {scales with frequency := frequency}
    let alternative := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.reference
    let velocity := fun source time =>
      biotSavart (quadrupoleDensity changed alternative time source) (patchCentroid alternative time receiver.1 receiver.2) -
        biotSavart (quadrupoleDensity changed reference time source) (patchCentroid reference time receiver.1 receiver.2)
    let input := fun time => (∑ source ∈ Finset.univ.erase receiver.1, velocity source time) - velocity adjacent time
    IntervalIntegrable (fun time => Real.exp (-weight * time) *
      (‖input time‖ / changed.location (receiver.1.val + 1))) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (‖input time‖ / changed.location (receiver.1.val + 1))) ≤
      (constant / changed.location (receiver.1.val + 1) ^ 4) * (216360000 * changed.hessian + 576 * changed.strain) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          ‖fun source : Fin count => if source.val ≤ receiver.1.val then
            changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖) +
        tolerance * changed.seed (receiver.1.val + 1) / weight := by
  obtain ⟨coarserCap, coarserPositive, constant, constantNonnegative, coarserFactory⟩ :=
    exists_uniform_actual_coarser_velocity_macro_feedback
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min coarserCap continuityCap
  have rawPositive : 0 < rawCap := lt_min coarserPositive continuityPositive
  refine ⟨rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive ratioPower tolerance tolerancePositive orbit sectionTime
    threshold referenceConstant scaleRoot factor boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne
    factorPositive factorSmall
  filter_upwards [coarserFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall
      referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_finer_patch_velocity_seed_tail amplitudePositive ratioBound alphaPositive ratioPower
      tolerancePositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_gt_atTop (0 : ℝ)] with frequency coarser finer frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver adjacent adjacentIdentity finish finishNonnegative
    finishBound weight weightPositive
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let alternative := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.reference
  let velocity := fun source time =>
    biotSavart (quadrupoleDensity changed alternative time source) (patchCentroid alternative time receiver.1 receiver.2) -
      biotSavart (quadrupoleDensity changed reference time source) (patchCentroid reference time receiver.1 receiver.2)
  let input := fun time => (∑ source ∈ Finset.univ.erase receiver.1, velocity source time) - velocity adjacent time
  let error := fun time => ‖input time‖ / changed.location (receiver.1.val + 1)
  let maskedState := fun time => ‖fun source : Fin count => if source.val ≤ receiver.1.val then
    changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖
  let coefficient := (constant / changed.location (receiver.1.val + 1) ^ 4) *
    (216360000 * changed.hessian + 576 * changed.strain)
  let remainder := tolerance * changed.seed (receiver.1.val + 1)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have locationPositive := changed.location_pos (receiver.1.val + 1)
  have fieldMeasurable (family : FiniteMovingPatchFamily (count * 4))
      (densities : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) (source : Fin count) :
      Measurable (fun time => biotSavart (quadrupoleDensity changed family.patchMotion time source)
        (patchCentroid family.patchMotion time receiver.1 receiver.2)) := by
    have joint : Measurable (fun point : ℝ × ℂ => biotSavart
        (quadrupoleDensity changed family.patchMotion point.1 source) point.2) :=
      measurable_biotSavart_of_measurable_vorticity (Parameter := ℝ)
      (vorticity := fun time => quadrupoleDensity changed family.patchMotion time source)
      (family.measurable_quadrupoleDensity changed densities source)
    have locationContinuous : Continuous (fun time : ℝ => patchCentroid family.patchMotion time receiver.1 receiver.2) :=
      family.patchCentroid_continuous (count := count) receiver.1 receiver.2
    have parameterMeasurable : Measurable (fun time : ℝ => (time, patchCentroid family.patchMotion time receiver.1 receiver.2)) :=
      measurable_id.prodMk locationContinuous.measurable
    with_reducible_and_instances
      simpa only [Function.comp_def] using joint.comp parameterMeasurable
  have velocityMeasurable (source : Fin count) : Measurable (velocity source) := by
    have first := fieldMeasurable prepared.trajectory.movingFamily prepared.densityIdentity source
    have second : Measurable (fun time => biotSavart (quadrupoleDensity changed reference time source)
        (patchCentroid reference time receiver.1 receiver.2)) := by
      dsimp only [reference]
      rw [prepared.referenceIdentity]
      exact fieldMeasurable prepared.referenceWitness.trajectory.movingFamily prepared.referenceWitness.densityIdentity source
    exact first.sub second
  have errorMeasurable : Measurable error :=
    ((Finset.measurable_sum _ (fun source _ => velocityMeasurable source)).sub (velocityMeasurable adjacent)).norm.div_const _
  have maskedContinuous : ContinuousOn maskedState (Icc 0 finish) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro source
    by_cases selected : source.val ≤ receiver.1.val
    · simp only [if_pos selected]
      exact continuousOn_const.mul ((stateContinuity prepared rawPositive (min_le_right _ _) path source).2.2.2.mono subset)
    · simp only [if_neg selected]
      exact continuousOn_const
  let enlarged := prepared.enlargeCap (min_le_left coarserCap continuityCap)
  have coarseBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.1.val), ‖velocity source time‖) /
        changed.location (receiver.1.val + 1) ≤ coefficient * maskedState time := by
    have actual := coarser count phase dipoleAngle enlarged path time (subset inside) receiver
    with_reducible_and_instances
      dsimp only [velocity, coefficient, maskedState, changed, alternative, reference,
        CascadeSourcePreparedPair.macroSourceState, enlarged, CascadeSourcePreparedPair.enlargeCap] at actual ⊢
      exact actual
  have fineBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      (∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.1.val + 2 ≤ source.val), ‖velocity source time‖) /
        changed.location (receiver.1.val + 1) ≤ remainder :=
    finer count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time (subset inside) receiver
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : error time ≤ coefficient * maskedState time + remainder := by
    have split := sum_erase_eq_lower_add_adjacent_add_finer receiver.1 adjacent adjacentIdentity (fun source => velocity source time)
    have identity : input time =
        (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.1.val), velocity source time) +
        ∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.1.val + 2 ≤ source.val), velocity source time := by
      dsimp only [input]
      rw [split]
      abel
    have triangle := (norm_add_le
      (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.1.val), velocity source time)
      (∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.1.val + 2 ≤ source.val), velocity source time)).trans
      (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
    rw [← identity] at triangle
    have divided := div_le_div_of_nonneg_right triangle locationPositive.le
    rw [add_div] at divided
    exact divided.trans (add_le_add (coarseBound time inside) (fineBound time inside))
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have upperContinuous : ContinuousOn (fun time => coefficient * maskedState time + remainder) (Icc 0 finish) :=
    (continuousOn_const.mul maskedContinuous).add continuousOn_const
  have majorantIntegrable := (exponentialContinuous.continuousOn.mul upperContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have errorIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * error time) volume 0 finish :=
    majorantIntegrable.mono_fun' (exponentialContinuous.measurable.mul errorMeasurable).aestronglyMeasurable.restrict (by
      rw [uIoc_of_le finishNonnegative]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with time inside
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (div_nonneg (norm_nonneg _) locationPositive.le))]
      exact mul_le_mul_of_nonneg_left (pointwise time ⟨inside.1.le, inside.2⟩) (Real.exp_pos _).le)
  have comparison := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative errorIntegrable majorantIntegrable
    (fun time inside => mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
  have maskedIntegrable := (exponentialContinuous.continuousOn.mul maskedContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have exponentialIntegrable := exponentialContinuous.intervalIntegrable (μ := volume) 0 finish
  have integralIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (coefficient * maskedState time + remainder)) =
      coefficient * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * maskedState time) +
        remainder * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) := by
    simp_rw [mul_add, mul_left_comm (Real.exp _) coefficient, mul_comm (Real.exp _) remainder]
    rw [intervalIntegral.integral_add (maskedIntegrable.const_mul _) (exponentialIntegrable.const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  have exponentialBound : weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time)) ≤ 1 := by
    have actual := laplace_affine_integral_bound (decay := weight) (slope := 0) (constant := 1)
      weightPositive (by norm_num) (by norm_num) finishNonnegative
    simp only [zero_mul, zero_add, mul_one, zero_div] at actual
    exact (mul_le_mul_of_nonneg_left actual weightPositive.le).trans_eq (by field_simp [weightPositive.ne'])
  have remainderNonnegative : 0 ≤ remainder := mul_nonneg tolerancePositive.le
    (changed.seed_pos frequencyPositive (by change 0 < scales.ratio; linarith only [ratioBound]) _).le
  have constantBound : remainder * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time)) ≤ remainder / weight := by
    apply (le_div_iff₀ weightPositive).mpr
    have actual := mul_le_mul_of_nonneg_left exponentialBound remainderNonnegative
    simpa only [mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using actual
  exact ⟨errorIntegrable, (comparison.trans_eq integralIdentity).trans (add_le_add_left constantBound _)⟩

end EulerNonuniqueness.Paper
