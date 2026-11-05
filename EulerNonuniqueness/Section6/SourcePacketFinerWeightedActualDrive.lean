import EulerNonuniqueness.Section6.SourcePacketFinerVectorActualDrive
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

private theorem weighted_constant_integral_identity {constant horizon weight : ℝ}
    (weightPositive : 0 < weight) :
    weight * (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * constant) =
      constant * (1 - Real.exp (-weight * horizon)) := by
  rw [intervalIntegral.integral_mul_const, integral_exp_mul_real (neg_ne_zero.mpr weightPositive.ne')]
  simp only [mul_zero, Real.exp_zero]
  field_simp [weightPositive.ne']
  ring

theorem Scales.eventually_actual_finer_source_weighted_seed_bound (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {tolerance : ℝ} (tolerancePositive : 0 < tolerance)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver : Fin count,
      ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop → ∀ weight : ℝ, 0 < weight →
      let changed : Scales := {scales with frequency := frequency}
      let input := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val),
        relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time
      IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖input time‖) volume 0 finish ∧
        weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖input time‖) ≤
          tolerance * changed.seed (receiver.val + 1) := by
  filter_upwards [scales.eventually_actual_finer_source_vector_seed_bound amplitudePositive ratioBound alphaPositive
      ratioPower tolerancePositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_gt_atTop (0 : ℝ)] with frequency fine regular frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver finish finishNonnegative finishBound weight weightPositive
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let selected := Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val)
  let input := fun time => ∑ source ∈ selected,
    relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time
  let constant := tolerance * changed.seed (receiver.val + 1)
  have constantNonnegative : 0 ≤ constant := mul_nonneg tolerancePositive.le
    (changed.seed_pos frequencyPositive (by dsimp only [changed]; linarith) _).le
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have inputContinuous : ContinuousOn input (Icc 0 finish) := by
    apply continuousOn_finset_sum selected
    intro source sourceMember
    have farther : receiver.val + 2 ≤ source.val := (Finset.mem_filter.mp sourceMember).2
    have different : receiver ≠ source := by
      intro same
      subst source
      omega
    exact (regular count phase dipoleAngle prepared path receiver source different).mono subset
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have inputIntegrable := (weightContinuous.continuousOn.mul inputContinuous.norm).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have constantIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * constant) volume 0 finish :=
    (weightContinuous.mul continuous_const).intervalIntegrable _ _
  have comparison := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative inputIntegrable constantIntegrable
    (fun time inside => mul_le_mul_of_nonneg_left
      (fine count phase dipoleAngle prepared path time (subset inside) receiver) (Real.exp_pos _).le)
  have weighted := mul_le_mul_of_nonneg_left comparison weightPositive.le
  rw [weighted_constant_integral_identity weightPositive] at weighted
  refine ⟨inputIntegrable, weighted.trans ?_⟩
  change constant * (1 - Real.exp (-weight * finish)) ≤ constant
  nlinarith [mul_nonneg constantNonnegative (Real.exp_pos (-weight * finish)).le]

end EulerNonuniqueness.Paper
