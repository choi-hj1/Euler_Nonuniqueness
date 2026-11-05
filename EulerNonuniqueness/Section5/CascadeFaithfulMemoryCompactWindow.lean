import EulerNonuniqueness.Section5.CascadePhysicalForeignForcingAbsoluteBound
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace


private theorem compact_memory_centered_state_continuous
    {rawCap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair) (index : Fin count) :
    ContinuousOn (fun time => prepared.rawSourceCenteredState time index) (Icc 0 path.stop) := by
  let first := prepared.referenceWitness.trajectory.movingFamily
  let final := prepared.trajectory.movingFamily
  have centroidContinuous (family : FiniteMovingPatchFamily (count * 4))
      (interior : ∀ label, Icc (0 : ℝ) path.stop ⊆ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (patch : Fin 4) :
      ContinuousOn (fun time => patchCentroid family.patchMotion time index patch) (Icc 0 path.stop) := by
    simp_rw [FiniteMovingPatchFamily.patchCentroid_eq]
    exact fun time inside => ((family.patch _).centroid_contDiffAt (interior _ inside)).continuousAt.continuousWithinAt
  have firstInterior (label : Fin (count * 4)) :
      Icc (0 : ℝ) path.stop ⊆ Ioo (first.patch label).initialTime (first.patch label).finalTime := by
    intro time inside
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have finalInterior (label : Fin (count * 4)) :
      Icc (0 : ℝ) path.stop ⊆ Ioo (final.patch label).initialTime (final.patch label).finalTime := by
    intro time inside
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have firstCenter : ContinuousOn (fun time => quadrupoleCenter first.patchMotion time index) (Icc 0 path.stop) :=
    (continuousOn_finset_sum _ fun patch _ => centroidContinuous first firstInterior patch).div_const 4
  have finalCenter : ContinuousOn (fun time => quadrupoleCenter final.patchMotion time index) (Icc 0 path.stop) :=
    (continuousOn_finset_sum _ fun patch _ => centroidContinuous final finalInterior patch).div_const 4
  have arrayContinuous : ContinuousOn (fun time =>
      (fun patch => patchCentroid first.patchMotion time index patch - quadrupoleCenter first.patchMotion time index) -
      (fun patch => patchCentroid final.patchMotion time index patch - quadrupoleCenter final.patchMotion time index))
      (Icc 0 path.stop) :=
    continuousOn_pi.mpr fun patch => ((centroidContinuous first firstInterior patch).sub firstCenter).sub
      ((centroidContinuous final finalInterior patch).sub finalCenter)
  exact arrayContinuous.norm.div_const _

private theorem compact_memory_kernel_identity (forcing : ℝ → ℝ) (rate start finish : ℝ) :
    (∫ current in start..finish, Real.exp (rate * (finish - current)) * forcing current) =
      Real.exp (rate * finish) * ∫ current in start..finish, Real.exp (-rate * current) * forcing current := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro current _
  change Real.exp (rate * (finish - current)) * forcing current =
    Real.exp (rate * finish) * (Real.exp (-rate * current) * forcing current)
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem compact_memory_properties {forcing : ℝ → ℝ} {horizon constant rate : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (constantNonnegative : 0 ≤ constant)
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (forcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time) :
    let memory := fun time => constant * ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * forcing current
    ContinuousOn memory (Icc 0 horizon) ∧
      IntervalIntegrable memory volume 0 horizon ∧ memory 0 = 0 ∧
      (∀ time ∈ Icc 0 horizon, 0 ≤ memory time) ∧
      ∀ start ∈ Icc 0 horizon, ∀ finish ∈ Icc start horizon,
        memory finish = Real.exp (rate * (finish - start)) * memory start +
          constant * ∫ current in start..finish, Real.exp (rate * (finish - current)) * forcing current := by
  dsimp only
  let weighted := fun current => Real.exp (-rate * current) * forcing current
  have exponential : Continuous (fun current : ℝ => Real.exp (-rate * current)) := by fun_prop
  have weightedContinuous : ContinuousOn weighted (Icc 0 horizon) :=
    exponential.continuousOn.mul forcingContinuous
  have weightedIntegrable := weightedContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have primitiveContinuous : ContinuousOn (fun time => ∫ current in (0 : ℝ)..time, weighted current) (Icc 0 horizon) := by
    simpa only [uIcc_of_le horizonNonnegative] using
      intervalIntegral.continuousOn_primitive_interval' weightedIntegrable left_mem_uIcc
  have memoryContinuous : ContinuousOn (fun time => constant * ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * forcing current) (Icc 0 horizon) := by
    simp_rw [compact_memory_kernel_identity]
    exact continuousOn_const.mul ((by fun_prop : Continuous (fun time : ℝ => Real.exp (rate * time))).continuousOn.mul primitiveContinuous)
  refine ⟨memoryContinuous, memoryContinuous.intervalIntegrable_of_Icc horizonNonnegative, by simp, ?_, ?_⟩
  · intro time inside
    exact mul_nonneg constantNonnegative (intervalIntegral.integral_nonneg inside.1 fun current member =>
      mul_nonneg (Real.exp_pos _).le (forcingNonnegative current ⟨member.1, member.2.trans inside.2⟩))
  · intro start startInside finish finishInside
    have firstIntegrable := (weightedContinuous.mono (Icc_subset_Icc le_rfl startInside.2)).intervalIntegrable_of_Icc (μ := volume) startInside.1
    have secondIntegrable := (weightedContinuous.mono (Icc_subset_Icc startInside.1 finishInside.2)).intervalIntegrable_of_Icc (μ := volume) finishInside.1
    have split := intervalIntegral.integral_add_adjacent_intervals firstIntegrable secondIntegrable
    simp_rw [compact_memory_kernel_identity]
    change constant * (Real.exp (rate * finish) * ∫ current in (0 : ℝ)..finish, weighted current) = _
    rw [← split]
    have product : Real.exp (rate * (finish - start)) * Real.exp (rate * start) = Real.exp (rate * finish) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change constant * (Real.exp (rate * finish) *
      ((∫ current in (0 : ℝ)..start, weighted current) + ∫ current in start..finish, weighted current)) =
      Real.exp (rate * (finish - start)) *
        (constant * (Real.exp (rate * start) * ∫ current in (0 : ℝ)..start, weighted current)) +
        constant * (Real.exp (rate * finish) * ∫ current in start..finish, weighted current)
    rw [show Real.exp (rate * (finish - start)) *
        (constant * (Real.exp (rate * start) * ∫ current in (0 : ℝ)..start, weighted current)) =
      constant * (Real.exp (rate * (finish - start)) * Real.exp (rate * start)) *
        (∫ current in (0 : ℝ)..start, weighted current) by ring, product]
    ring


theorem exists_uniform_actual_faithful_memory_compact_window :
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 → ∃ foreignConstant ≥ (0 : ℝ),
    ∀ memoryConstant : ℝ, 0 ≤ memoryConstant → ∀ extent ≥ (1 : ℝ), ∀ span ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {rawCap shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ index : Fin count,
    let changed : Scales := {scales with frequency := frequency}
    let omega := changed.omega (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let centered := fun time => prepared.rawSourceCenteredState time index
    let foreign := prepared.physicalForeignSourceForcing index
    let drive := fun time => omega * centered time + foreign time
    let rate := memoryConstant * (1 + omega * epsilon)
    let memory := fun time => memoryConstant * ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * drive current
    0 ≤ rate ∧ rate ≤ 2 * memoryConstant ∧ rate * span / omega ≤ 1 ∧
    ContinuousOn centered (Icc 0 path.stop) ∧ ContinuousOn foreign (Icc 0 path.stop) ∧
    ContinuousOn drive (Icc 0 path.stop) ∧ ContinuousOn memory (Icc 0 path.stop) ∧
    IntervalIntegrable drive volume 0 path.stop ∧ IntervalIntegrable memory volume 0 path.stop ∧
    memory 0 = 0 ∧
    (∀ time ∈ Icc 0 path.stop, 0 ≤ memory time ∧ 0 ≤ foreign time ∧ foreign time ≤ foreignConstant * changed.strain) ∧
    ∀ start ∈ Icc 0 path.stop, ∀ finish ∈ Icc start path.stop,
      memory finish = Real.exp (rate * (finish - start)) * memory start +
        memoryConstant * ∫ current in start..finish, Real.exp (rate * (finish - current)) * drive current ∧
      IntervalIntegrable drive volume start finish ∧
      IntervalIntegrable (fun current => Real.exp (rate * (finish - current)) * drive current) volume start finish ∧
      (omega * (finish - start) ≤ span →
        (∀ time ∈ Icc start finish, ∀ patch,
          ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
            quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤ extent * changed.length (index.val + 1)) →
        (∀ time ∈ Icc start finish, ∀ patch,
          ‖patchCentroid prepared.reference time index patch - quadrupoleCenter prepared.reference time index‖ ≤
            extent * changed.length (index.val + 1)) →
        (∀ time ∈ Icc start finish, centered time ≤ 2 * extent) ∧
        memory finish ≤ Real.exp 1 * (memory start +
          memoryConstant * (2 * extent * span + foreignConstant * changed.strain * span / omega))) := by

  intro factor factorPositive factorSmall
  obtain ⟨foreignConstant, foreignConstantNonnegative, absoluteBounds⟩ :=
    exists_uniform_actual_physical_foreign_forcing_absolute_bound factor factorPositive factorSmall
  refine ⟨foreignConstant, foreignConstantNonnegative, ?_⟩
  intro memoryConstant memoryConstantNonnegative extent extentOne span spanNonnegative scales amplitudePositive ratioBound alphaPositive
    orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne
  filter_upwards [absoluteBounds scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_cascade_physical_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_ge_atTop (max 1 (max (2 / scales.amplitude) (2 * memoryConstant * span)))]
    with frequency absoluteEstimate foreignContinuity frequencyLarge
  intro count phase dipoleAngle rawCap shapeRadius monitor prepared path index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let centered := fun time => prepared.rawSourceCenteredState time index
  let foreign := prepared.physicalForeignSourceForcing index
  let drive := fun time => omega * centered time + foreign time
  let rate := memoryConstant * (1 + omega * epsilon)
  let memory := fun time => memoryConstant * ∫ current in (0 : ℝ)..time,
    Real.exp (rate * (time - current)) * drive current
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
  have ratioPositive : 0 < changed.ratio := zero_lt_one.trans_le ratioOne
  have frequencyOmega : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive ratioOne _
  have omegaOne : 1 ≤ omega := frequencyOne.trans frequencyOmega
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have amplitudeOmega : 2 / scales.amplitude ≤ omega :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (frequencyLarge.trans frequencyOmega)
  have spanOmega : 2 * memoryConstant * span ≤ omega :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (frequencyLarge.trans frequencyOmega)
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have omegaEpsilonIdentity : omega * epsilon = 2 / (changed.amplitude * omega ^ 2) := by
    dsimp only [epsilon]
    rw [changed.radius_sq amplitudePositive frequencyPositive ratioPositive]
    dsimp only [omega]
    field_simp [(changed.length_pos (index.val + 1)).ne', amplitudePositive.ne', omegaPositive.ne']
    ring
  have denominatorLower : 2 ≤ changed.amplitude * omega ^ 2 := by
    have linearLower : 2 ≤ changed.amplitude * omega := by
      have actual := (div_le_iff₀ amplitudePositive).mp amplitudeOmega
      simpa only [mul_comm] using actual
    have omegaSquare : omega ≤ omega ^ 2 := by nlinarith only [omegaOne]
    exact linearLower.trans (mul_le_mul_of_nonneg_left omegaSquare amplitudePositive.le)
  have omegaEpsilonSmall : omega * epsilon ≤ 1 := by
    rw [omegaEpsilonIdentity]
    exact (div_le_one (by positivity : 0 < changed.amplitude * omega ^ 2)).mpr denominatorLower
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have rateBound : rate ≤ 2 * memoryConstant := by
    have scaled := mul_le_mul_of_nonneg_left omegaEpsilonSmall memoryConstantNonnegative
    dsimp only [rate]
    linarith only [scaled]
  have rateMargin : rate * span / omega ≤ 1 := by
    apply (div_le_one omegaPositive).mpr
    exact (mul_le_mul_of_nonneg_right rateBound spanNonnegative).trans spanOmega
  have centeredContinuous : ContinuousOn centered (Icc 0 path.stop) := compact_memory_centered_state_continuous prepared path index
  have foreignActual := foreignContinuity count phase dipoleAngle prepared path index
  have foreignContinuous : ContinuousOn foreign (Icc 0 path.stop) := foreignActual.2.1
  have driveContinuous : ContinuousOn drive (Icc 0 path.stop) :=
    (continuousOn_const.mul centeredContinuous).add foreignContinuous
  have centeredNonnegative (time : ℝ) : 0 ≤ centered time :=
    div_nonneg (norm_nonneg _) (changed.length_pos _).le
  have driveNonnegative (time : ℝ) : 0 ≤ drive time :=
    add_nonneg (mul_nonneg omegaPositive.le (centeredNonnegative time)) (prepared.physicalForeignSourceForcing_nonneg index time)
  have memoryProperties := compact_memory_properties (rate := rate) path.stopPositive.le memoryConstantNonnegative driveContinuous
    (fun time _ => driveNonnegative time)
  change ContinuousOn memory (Icc 0 path.stop) ∧ IntervalIntegrable memory volume 0 path.stop ∧
    memory 0 = 0 ∧ (∀ time ∈ Icc 0 path.stop, 0 ≤ memory time) ∧ _ at memoryProperties
  have absolute (time : ℝ) (inside : time ∈ Icc 0 path.stop) : 0 ≤ foreign time ∧ foreign time ≤ foreignConstant * changed.strain :=
    (absoluteEstimate count orbit sectionTime phase dipoleAngle prepared path index time inside).2
  refine ⟨rateNonnegative, rateBound, rateMargin, centeredContinuous, foreignContinuous, driveContinuous,
    memoryProperties.1, driveContinuous.intervalIntegrable_of_Icc path.stopPositive.le, memoryProperties.2.1,
    memoryProperties.2.2.1, fun time inside => ⟨memoryProperties.2.2.2.1 time inside, (absolute time inside).1, (absolute time inside).2⟩, ?_⟩
  intro start startInside finish finishInside
  have subset : Icc start finish ⊆ Icc 0 path.stop := Icc_subset_Icc startInside.1 finishInside.2
  have driveIntegrable := (driveContinuous.mono subset).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have kernelContinuous : Continuous (fun current : ℝ => Real.exp (rate * (finish - current))) := by fun_prop
  have kernelIntegrable := (kernelContinuous.continuousOn.mul (driveContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have split := memoryProperties.2.2.2.2 start startInside finish finishInside
  refine ⟨split, driveIntegrable, kernelIntegrable, ?_⟩
  intro normalizedSpan firstExtent secondExtent
  have extentNonnegative : 0 ≤ extent := zero_le_one.trans extentOne
  have lengthPositive := changed.length_pos (index.val + 1)
  have centeredBound (time : ℝ) (inside : time ∈ Icc start finish) : centered time ≤ 2 * extent := by
    dsimp only [centered, CascadeSourcePreparedPair.rawSourceCenteredState]
    apply (div_le_iff₀ lengthPositive).mpr
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (2 * extent) * changed.length (index.val + 1))).mpr
    intro patch
    rw [← prepared.referenceIdentity]
    have triangle := norm_sub_le
      (patchCentroid prepared.reference time index patch - quadrupoleCenter prepared.reference time index)
      (patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch - quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)
    exact triangle.trans ((add_le_add (secondExtent time inside patch) (firstExtent time inside patch)).trans_eq (by ring))
  have durationBound : finish - start ≤ span / omega := by
    apply (le_div_iff₀ omegaPositive).mpr
    simpa only [mul_comm] using normalizedSpan
  have rateDuration : rate * (finish - start) ≤ 1 := by
    calc
      _ ≤ rate * (span / omega) := mul_le_mul_of_nonneg_left durationBound rateNonnegative
      _ = rate * span / omega := by ring
      _ ≤ 1 := rateMargin
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have inputNonnegative : 0 ≤ omega * (2 * extent) + foreignConstant * changed.strain := by positivity
  have kernelInputBound (current : ℝ) (inside : current ∈ Icc start finish) :
      Real.exp (rate * (finish - current)) * drive current ≤
        Real.exp 1 * (omega * (2 * extent) + foreignConstant * changed.strain) := by
    have exponentialBound : Real.exp (rate * (finish - current)) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left (sub_le_sub_left inside.1 finish) rateNonnegative).trans rateDuration)
    have inputBound : drive current ≤ omega * (2 * extent) + foreignConstant * changed.strain :=
      add_le_add (mul_le_mul_of_nonneg_left (centeredBound current inside) omegaPositive.le) (absolute current (subset inside)).2
    exact mul_le_mul exponentialBound inputBound (driveNonnegative current) (Real.exp_pos _).le
  have comparison := intervalIntegral.integral_mono_on finishInside.1 kernelIntegrable
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.exp 1 * (omega * (2 * extent) + foreignConstant * changed.strain)) volume start finish)
    kernelInputBound
  rw [intervalIntegral.integral_const, smul_eq_mul] at comparison
  have windowBound : (∫ current in start..finish, Real.exp (rate * (finish - current)) * drive current) ≤
      Real.exp 1 * (2 * extent * span + foreignConstant * changed.strain * span / omega) := by
    apply comparison.trans
    calc
      (finish - start) * (Real.exp 1 * (omega * (2 * extent) + foreignConstant * changed.strain)) ≤
          (span / omega) * (Real.exp 1 * (omega * (2 * extent) + foreignConstant * changed.strain)) :=
        mul_le_mul_of_nonneg_right durationBound (mul_nonneg (Real.exp_pos _).le inputNonnegative)
      _ = Real.exp 1 * (2 * extent * span + foreignConstant * changed.strain * span / omega) := by
        field_simp [omegaPositive.ne']
        ring
  have initialBound := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr rateDuration)
    (memoryProperties.2.2.2.1 start startInside)
  have forcingBound := mul_le_mul_of_nonneg_left windowBound memoryConstantNonnegative
  refine ⟨centeredBound, ?_⟩
  change memory finish ≤ Real.exp 1 * (memory start +
    memoryConstant * (2 * extent * span + foreignConstant * changed.strain * span / omega))
  exact split.trans_le ((add_le_add initialBound forcingBound).trans_eq (by ring))

end EulerNonuniqueness.Paper
