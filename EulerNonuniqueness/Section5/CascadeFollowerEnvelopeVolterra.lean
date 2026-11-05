import EulerNonuniqueness.Section5.CascadeMacroSourceCoarseResponse
import EulerNonuniqueness.Section5.CascadeSelectedForeignForcingContinuity
import EulerNonuniqueness.Section5.CascadeFollowerForcingRow
import EulerNonuniqueness.Section1.CoarseFollowerRateGap
import EulerNonuniqueness.General.MaskedExponentialVolterra

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def CascadeSourcePreparedPair.followerRemainingForcing
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ}
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (drive : Fin count) (time : ℝ) : ℝ :=
  ‖fun receiver : Fin count => if receiver.val < drive.val then
    scales.location (receiver.val + 1) ^ 4 * prepared.selectedForeignForcing
      (Finset.univ.filter (fun source : Fin count => drive.val ≤ source.val ∧ source ≠ receiver)) receiver time else 0‖

theorem exists_uniform_actual_follower_envelope_volterra :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (2 * constant) ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ,
    threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ drive : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time receiver| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time receiver| ≤ radius) →
    let changed : Scales := {scales with frequency := frequency}
    let envelope := prepared.coarserFollowerEnvelope drive
    let remaining := prepared.followerRemainingForcing drive
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let growth := constant * changed.omega (drive.val + 1) / changed.ratio
    ContinuousOn envelope (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
    IntervalIntegrable envelope volume 0 finish ∧ IntervalIntegrable remaining volume 0 finish ∧
    envelope 0 = 0 ∧
    ∀ time ∈ Icc 0 finish,
      IntervalIntegrable (fun current => Real.exp (growth * (time - current)) *
        (rho * envelope current + remaining current)) volume 0 time ∧
      envelope time ≤ constant * ∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * (rho * envelope current + remaining current) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, macroCap, macroPositive, macroFactory⟩ :=
    exists_uniform_actual_macro_source_coarse_response
  obtain ⟨rowCap, rowPositive, rowConstant, rowNonnegative, rowFactory⟩ := exists_uniform_actual_follower_forcing_row
  obtain ⟨partitionCap, partitionPositive, partitionFactory⟩ := exists_uniform_actual_foreign_forcing_partition
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min macroCap (min rowCap (min partitionCap continuityCap))
  have rawPositive : 0 < rawCap := lt_min macroPositive (lt_min rowPositive (lt_min partitionPositive continuityPositive))
  have macroCapBound : rawCap ≤ macroCap := min_le_left _ _
  have rowCapBound : rawCap ≤ rowCap := (min_le_right _ _).trans (min_le_left _ _)
  have partitionCapBound : rawCap ≤ partitionCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have continuityCapBound : rawCap ≤ continuityCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, macroConstant, macroOne, rootMin, rootEight, macros⟩ :=
    macroFactory factorPositive factorSmall
  let constant := macroConstant * (1 + rowConstant)
  have macroNonnegative : 0 ≤ macroConstant := zero_le_one.trans macroOne
  have macroBelow : macroConstant ≤ constant := by dsimp only [constant]; nlinarith only [mul_nonneg macroNonnegative rowNonnegative]
  have constantOne : 1 ≤ constant := macroOne.trans macroBelow
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  have rowProductBelow : macroConstant * rowConstant ≤ constant := by dsimp only [constant]; nlinarith only [macroNonnegative]
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne orbit sectionTime
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  have factorOne : factor ≤ 1 := by linarith only [factorSmall]
  filter_upwards [macros scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant
      boundaryConstant thresholdBound referenceNonnegative boundaryOne orbit sectionTime,
    rowFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorSmall,
    partitionFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_selected_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_ge_atTop (1 : ℝ)] with frequency macroEstimate rowEstimate partitionEstimate selectedContinuous frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path drive finish finishNonnegative finishBound small
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let followers := Finset.univ.filter (fun receiver : Fin count => receiver.val < drive.val)
  let external := fun receiver : Fin count => Finset.univ.filter
    (fun source : Fin count => drive.val ≤ source.val ∧ source ≠ receiver)
  let envelope := prepared.coarserFollowerEnvelope drive
  let remaining := prepared.followerRemainingForcing drive
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let growth := constant * changed.omega (drive.val + 1) / changed.ratio
  let fullForcing := fun receiver time => prepared.finiteCoordinateForeignForcing receiver time +
    prepared.physicalForeignSourceForcing receiver time
  let inputs := fun receiver time => changed.location (receiver.val + 1) ^ 4 * fullForcing receiver time
  let states := fun receiver time => prepared.weightedMacroSourceState time receiver
  have macroCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have selectedCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have forcingCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateForeignForcing = prepared.finiteCoordinateForeignForcing := rfl
  have physicalCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).physicalForeignSourceForcing = prepared.physicalForeignSourceForcing := rfl
  have envelopeCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).coarserFollowerEnvelope = prepared.coarserFollowerEnvelope := by
    funext currentDrive current
    simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState, macroCapInvariant]
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]
    positivity
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have stateContinuous (receiver : Fin count) : ContinuousOn (states receiver) (Icc 0 finish) :=
    continuousOn_const.mul (((stateContinuity prepared rawPositive continuityCapBound path receiver).2.2.2).mono subset)
  have envelopeContinuous : ContinuousOn envelope (Icc 0 finish) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro receiver
    by_cases below : receiver.val < drive.val
    · simpa only [below, ite_true] using stateContinuous receiver
    · simpa only [below, ite_false] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 finish))
  have externalSubset (receiver : Fin count) : external receiver ⊆ Finset.univ.erase receiver := by
    intro source member
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp member).2.2, Finset.mem_univ _⟩
  have selectedData (receiver : Fin count) := selectedContinuous count phase dipoleAngle prepared path receiver
    (external receiver) (externalSubset receiver)
  have remainingContinuous : ContinuousOn remaining (Icc 0 finish) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro receiver
    by_cases below : receiver.val < drive.val
    · simpa only [below, ite_true] using
        (continuousOn_const.mul ((selectedData receiver).2.1.mono subset) :
          ContinuousOn (fun current => changed.location (receiver.val + 1) ^ 4 *
            prepared.selectedForeignForcing (external receiver) receiver current) (Icc 0 finish))
    · simpa only [below, ite_false] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 finish))
  have envelopeNonnegative (time : ℝ) : 0 ≤ envelope time := norm_nonneg _
  have remainingNonnegative (time : ℝ) : 0 ≤ remaining time := norm_nonneg _
  have memberBelow (receiver : Fin count) (member : receiver ∈ followers) : receiver.val < drive.val :=
    (Finset.mem_filter.mp member).2
  have sourceData (receiver : Fin count) (member : receiver ∈ followers) :
      ContinuousOn (fullForcing receiver) (Icc 0 finish) ∧
      ∀ time ∈ Icc 0 finish, prepared.macroSourceState time receiver ≤ macroConstant * ∫ current in (0 : ℝ)..time,
        Real.exp (macroConstant * changed.omega (receiver.val + 1) * (time - current)) * fullForcing receiver current := by
    have below := memberBelow receiver member
    have nonterminal : receiver.val + 1 < count := by omega
    have actual := macroEstimate count phase dipoleAngle (prepared.enlargeCap macroCapBound) path receiver nonterminal
      finish finishNonnegative finishBound (small receiver below)
    dsimp only at actual
    simp only [macroCapInvariant, forcingCapInvariant, physicalCapInvariant] at actual
    exact ⟨actual.1, fun time inside => (actual.2.2 time inside).2⟩
  have inputsContinuous (receiver : Fin count) (member : receiver ∈ followers) :
      ContinuousOn (inputs receiver) (Icc 0 finish) := continuousOn_const.mul (sourceData receiver member).1
  have inputsBound (receiver : Fin count) (member : receiver ∈ followers) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      inputs receiver time ≤ rowConstant * rho * envelope time + remaining time := by
    have below := memberBelow receiver member
    have different : receiver ≠ drive := by intro same; subst receiver; omega
    obtain ⟨_, _, partitionBound⟩ := partitionEstimate count phase dipoleAngle
      (prepared.enlargeCap partitionCapBound) path (subset inside) receiver drive
    simp only [forcingCapInvariant, physicalCapInvariant, selectedCapInvariant] at partitionBound
    obtain ⟨_, _, _, rowBound⟩ := rowEstimate count phase dipoleAngle (prepared.enlargeCap rowCapBound) path
      time (subset inside) receiver drive below.le
    simp only [selectedCapInvariant, envelopeCapInvariant, different, ite_false, add_zero] at rowBound
    have remainingComponent : changed.location (receiver.val + 1) ^ 4 *
        prepared.selectedForeignForcing (external receiver) receiver time ≤ remaining time := by
      have actual := norm_le_pi_norm (fun currentReceiver : Fin count => if currentReceiver.val < drive.val then
        changed.location (currentReceiver.val + 1) ^ 4 *
          prepared.selectedForeignForcing (external currentReceiver) currentReceiver time else 0) receiver
      have componentNonnegative : 0 ≤ changed.location (receiver.val + 1) ^ 4 *
          prepared.selectedForeignForcing (external receiver) receiver time :=
        mul_nonneg (pow_nonneg (changed.location_pos _).le 4) ((selectedData receiver).1 time)
      simpa only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg componentNonnegative] using actual
    have scaledPartition := mul_le_mul_of_nonneg_left partitionBound (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
    apply scaledPartition.trans
    rw [mul_add]
    exact add_le_add rowBound remainingComponent
  have forcingContinuous : ContinuousOn (fun time => rowConstant * rho * envelope time + remaining time) (Icc 0 finish) :=
    (continuousOn_const.mul envelopeContinuous).add remainingContinuous
  have forcingNonnegative (time : ℝ) : 0 ≤ rowConstant * rho * envelope time + remaining time :=
    add_nonneg (mul_nonneg (mul_nonneg rowNonnegative rhoNonnegative) (envelopeNonnegative time)) (remainingNonnegative time)
  have propagator (receiver : Fin count) (member : receiver ∈ followers) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      states receiver time ≤ macroConstant * ∫ current in (0 : ℝ)..time,
        Real.exp (macroConstant * changed.omega (receiver.val + 1) * (time - current)) * inputs receiver current := by
    have actual := mul_le_mul_of_nonneg_left ((sourceData receiver member).2 time inside)
      (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
    have integralIdentity : (∫ current in (0 : ℝ)..time,
        Real.exp (macroConstant * changed.omega (receiver.val + 1) * (time - current)) * inputs receiver current) =
        changed.location (receiver.val + 1) ^ 4 * ∫ current in (0 : ℝ)..time,
          Real.exp (macroConstant * changed.omega (receiver.val + 1) * (time - current)) * fullForcing receiver current := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro current _
      dsimp only [inputs]
      ring
    rw [integralIdentity]
    convert actual using 1; ring
  have ratesBound (receiver : Fin count) (member : receiver ∈ followers) :
      macroConstant * changed.omega (receiver.val + 1) ≤ growth := by
    have omegaNonnegative := (changed.omega_pos frequencyPositive ratioPositive (receiver.val + 1)).le
    exact (mul_le_mul_of_nonneg_right macroBelow omegaNonnegative).trans
      ((changed.coarse_follower_rate_gap constant frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound])
        constantNonnegative receiver.val drive.val (memberBelow receiver member)).2.1)
  have masked := General.norm_masked_exponential_volterra_le followers inputsContinuous forcingContinuous macroNonnegative
    (fun receiver _ time _ => mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time receiver))
    (fun time _ => forcingNonnegative time) ratesBound inputsBound propagator
  have preliminary (time : ℝ) (inside : time ∈ Icc 0 finish) :
      envelope time ≤ macroConstant * ∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * (rowConstant * rho * envelope current + remaining current) := by
    simpa only [followers, Finset.mem_filter, Finset.mem_univ, true_and] using masked time inside
  have targetContinuous : ContinuousOn (fun current => rho * envelope current + remaining current) (Icc 0 finish) :=
    (continuousOn_const.mul envelopeContinuous).add remainingContinuous
  have conclusion (time : ℝ) (inside : time ∈ Icc 0 finish) :
      IntervalIntegrable (fun current => Real.exp (growth * (time - current)) *
        (rho * envelope current + remaining current)) volume 0 time ∧
      envelope time ≤ constant * ∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * (rho * envelope current + remaining current) := by
    have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have kernel : Continuous (fun current : ℝ => Real.exp (growth * (time - current))) := by fun_prop
    have originalIntegrable := (kernel.continuousOn.mul (forcingContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    have targetIntegrable := (kernel.continuousOn.mul (targetContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    have comparison := intervalIntegral.integral_mono_on inside.1 (originalIntegrable.const_mul macroConstant)
      (targetIntegrable.const_mul constant) (by
        intro current _
        have first := mul_le_mul_of_nonneg_right rowProductBelow (mul_nonneg rhoNonnegative (envelopeNonnegative current))
        have second := mul_le_mul_of_nonneg_right macroBelow (remainingNonnegative current)
        have point := add_le_add first second
        have scaled := mul_le_mul_of_nonneg_left point (Real.exp_pos (growth * (time - current))).le
        convert scaled using 1 <;> ring)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at comparison
    exact ⟨targetIntegrable, (preliminary time inside).trans comparison⟩
  have initial : envelope 0 = 0 := le_antisymm (by simpa only [intervalIntegral.integral_same, mul_zero] using
    (conclusion 0 ⟨le_rfl, finishNonnegative⟩).2) (envelopeNonnegative 0)
  exact ⟨envelopeContinuous, remainingContinuous, envelopeContinuous.intervalIntegrable_of_Icc finishNonnegative,
    remainingContinuous.intervalIntegrable_of_Icc finishNonnegative, initial, conclusion⟩

end EulerNonuniqueness.Paper
