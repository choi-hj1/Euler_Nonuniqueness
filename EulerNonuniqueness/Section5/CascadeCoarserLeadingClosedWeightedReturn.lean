import EulerNonuniqueness.Section5.CascadeCoarserLeadingActualFeedback
import EulerNonuniqueness.Section5.CascadeFollowerEnvelopeArbitraryWeightReturn
import EulerNonuniqueness.Section5.CascadeMixedFollowerClosedPrefixBudget
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity
import EulerNonuniqueness.General.FinitePrefixMask

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem coarser_leading_closed_scalar
    {action envelope driver remaining macroValue common coarse responseE responseK rho distance weight : ℝ}
    (distancePositive : 0 < distance) (weightPositive : 0 < weight)
    (coarseNonnegative : 0 ≤ coarse) (responseNonnegative : 0 ≤ responseE) (rhoNonnegative : 0 ≤ rho)
    (actionBound : action ≤ coarse / distance ^ 4 * rho * (envelope + driver))
    (envelopeBound : envelope ≤ (2 * responseE / weight) * (rho * driver + remaining))
    (remainingBound : remaining ≤ 2 * common + (4 * responseK / weight) * driver)
    (driverIdentity : driver = distance ^ 4 * macroValue) :
    action ≤ (4 * coarse * responseE * rho / (weight * distance ^ 4)) * common +
      coarse * rho * (1 + 2 * responseE * rho / weight + 8 * responseE * responseK / weight ^ 2) * macroValue := by
  have envelopeClosed := envelopeBound.trans (mul_le_mul_of_nonneg_left
    (add_le_add_left remainingBound (rho * driver))
    (div_nonneg (mul_nonneg (by norm_num) responseNonnegative) weightPositive.le))
  have scaled := mul_le_mul_of_nonneg_left (add_le_add_right envelopeClosed driver)
    (mul_nonneg (div_nonneg coarseNonnegative (pow_nonneg distancePositive.le 4)) rhoNonnegative)
  have result := actionBound.trans scaled
  rw [driverIdentity] at result
  convert result using 1
  field_simp [distancePositive.ne', weightPositive.ne']
  ring

theorem exists_uniform_actual_coarser_leading_closed_weighted_return :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ coarseConstant ≥ (0 : ℝ), ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseE ≥ (1 : ℝ), ∃ responseK ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ accuracy : ℝ, 0 < accuracy →
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (max (2 * responseE) (4 * responseK)) ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant : ℝ), 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver : Fin count, receiver.val + 1 < count →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, receiver.val < source.val →
      let length := changed.length (source.val + 1)
      0 ≤ entry source ∧ entry source ≤ path.stop ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entry source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion (entry source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
          secondDipoleCenter motion (entry source) source)).re ∧
      ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
        (5 / 4 : ℝ) * length * initialDistance source) →
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source),
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
        extent * changed.length (source.val + 1))) →
    ∀ coefficient : ℝ, 0 < coefficient → ∀ magnitude : Fin count → ℝ,
    let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    (∀ source : Fin count, receiver.val < source.val → 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
        magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    ∀ finish ∈ Icc 0 path.stop,
    (∀ current : Fin count, current.val < receiver.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time current| + |stableShape motion time current| ≤ radius) →
    ∀ weight : ℝ, 2 * changed.omega (receiver.val + 1) ≤ weight →
    (∀ source : Fin count, receiver.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let coarseInput := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
      relativeBlockSourceShapeInput changed motion prepared.reference receiver source time
    let macroValue := fun time => prepared.macroSourceState time receiver
    let finer := Finset.univ.filter (fun source : Fin count => receiver.val < source.val)
    let commonBudget := incomingConstant * extent ^ 2 * (∑ source ∈ finer,
      changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
        (1 + (changed.location (source.val + 1))⁻¹) * magnitude source /
        (coefficient * changed.omega (source.val + 1)) * Real.exp (-weight * entry source)) +
      outgoingConstant * (∑ source ∈ finer.filter (fun source => entry source < finish),
        changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) / weight ^ 2 +
          ((1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
            ‖centroidAsymmetry motion (entry source) source‖) / weight) * Real.exp (-weight * entry source))
    ContinuousOn coarseInput (Icc 0 path.stop) ∧ ContinuousOn macroValue (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) • coarseInput time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖coarseInput time‖) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * macroValue time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖coarseInput time‖) ≤
      accuracy * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * macroValue time) +
      (4 * coarseConstant * responseE * (216360000 * changed.hessian + 576 * changed.strain) /
        (weight * changed.location (receiver.val + 1) ^ 4)) * commonBudget := by
  classical
  obtain ⟨coarseCap, coarseCapPositive, coarseConstant, coarseNonnegative, coarses⟩ :=
    exists_uniform_actual_coarser_leading_actual_feedback
  obtain ⟨envelopeThreshold, envelopeThresholdPositive, envelopeEighth, envelopeCap, envelopeCapPositive, envelopes⟩ :=
    exists_uniform_actual_follower_envelope_arbitrary_weight_return
  obtain ⟨remainingThreshold, remainingThresholdPositive, _, remainingCap, remainingCapPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, remainings⟩ :=
    exists_uniform_actual_mixed_follower_closed_prefix_budget
  let rawCap := min coarseCap (min envelopeCap remainingCap)
  have coarseCapBound : rawCap ≤ coarseCap := min_le_left _ _
  have envelopeCapBound : rawCap ≤ envelopeCap := (min_le_right _ _).trans (min_le_left _ _)
  have remainingCapBound : rawCap ≤ remainingCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min envelopeThreshold remainingThreshold, lt_min envelopeThresholdPositive remainingThresholdPositive,
    (min_le_left _ _).trans envelopeEighth, rawCap, lt_min coarseCapPositive (lt_min envelopeCapPositive remainingCapPositive),
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨envelopeRadius, envelopeRadiusPositive, envelopeQuarter, responseE, responseEOne, rootE, rootEEight, envelopeFactory⟩ :=
    envelopes factorPositive factorSmall
  obtain ⟨remainingRadius, remainingRadiusPositive, _, responseK, responseKOne, rootK, rootKEight, remainingFactory⟩ :=
    remainings factorPositive factorSmall
  refine ⟨min envelopeRadius remainingRadius, lt_min envelopeRadiusPositive remainingRadiusPositive,
    (min_le_left _ _).trans envelopeQuarter, responseE, responseEOne, responseK, responseKOne,
    max rootE rootK, rootEEight.trans (le_max_left _ _), ?_⟩
  intro extent extentOne accuracy accuracyPositive scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant boundaryOne
  have rootELarge : rootE ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have rootKLarge : rootK ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEEight.trans rootELarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioE : max 2 (2 * responseE) ≤ scales.ratio := max_le ratioBound
    ((le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge))
  have ratioK : max 2 (4 * responseK) ≤ scales.ratio := max_le ratioBound
    ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge))
  have thresholdSmall : threshold ≤ 1 / 8 := (thresholdBound.trans (min_le_left _ _)).trans envelopeEighth
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  let rhoAt := fun frequency : ℝ => 216360000 * ({scales with frequency := frequency} : Scales).hessian +
    576 * ({scales with frequency := frequency} : Scales).strain
  have rhoDecay : Tendsto rhoAt atTop (𝓝 0) := by
    simpa only [rhoAt, mul_zero, zero_add] using
      (((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576))
  have coefficientDecay : Tendsto (fun frequency => coarseConstant * rhoAt frequency *
      (1 + 2 * responseE * rhoAt frequency + 8 * responseE * responseK)) atTop (𝓝 0) := by
    have regular : Continuous (fun value : ℝ => coarseConstant * value *
      (1 + 2 * responseE * value + 8 * responseE * responseK)) := by fun_prop
    simpa only [mul_zero, zero_mul] using (regular.tendsto 0).comp rhoDecay
  filter_upwards [coarses scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorOne,
    envelopeFactory scales scaleRoot rootELarge amplitudeIdentity ratioE alphaPositive threshold referenceConstant boundaryConstant
      (thresholdBound.trans (min_le_left _ _)) referenceNonnegative boundaryOne orbit sectionTime,
    remainingFactory scales scaleRoot rootKLarge amplitudeIdentity ratioK alphaPositive extent extentOne referenceConstant referenceNonnegative
      referenceAmplitude threshold (thresholdBound.trans (min_le_right _ _)) orbit sectionTime boundaryConstant boundaryOne,
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    coefficientDecay.eventually (eventually_lt_nhds accuracyPositive),
    eventually_ge_atTop (1 : ℝ)] with frequency coarseEstimate envelopeEstimate remainingEstimate inputContinuous coefficientSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance direction
  dsimp only
  intro entries extents coefficient coefficientPositive magnitude profiles finish finishInside small weight weightLower rateBounds
  let changed : Scales := {scales with frequency := frequency}
  let location := changed.location (receiver.val + 1)
  let rho := rhoAt frequency
  let envelope := prepared.coarserFollowerEnvelope receiver
  let driver := fun time => prepared.weightedMacroSourceState time receiver
  let remaining := prepared.followerStrictlyFinerForcing receiver
  let macroValue := fun time => prepared.macroSourceState time receiver
  let coarseInput := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
    relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time
  let finer := Finset.univ.filter (fun source : Fin count => receiver.val < source.val)
  let commonBudget := incomingConstant * extent ^ 2 * (∑ source ∈ finer,
    changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
      (1 + (changed.location (source.val + 1))⁻¹) * magnitude source /
      (coefficient * changed.omega (source.val + 1)) * Real.exp (-weight * entry source)) +
    outgoingConstant * (∑ source ∈ finer.filter (fun source => entry source < finish),
      changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) / weight ^ 2 +
        ((1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
          ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion (entry source) source‖) / weight) * Real.exp (-weight * entry source))
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaOne : 1 ≤ changed.omega (receiver.val + 1) := frequencyOne.trans
    (le_mul_of_one_le_right frequencyPositive.le (one_le_pow₀ (by change 1 ≤ scales.ratio; linarith only [ratioBound])))
  have weightOne : 1 ≤ weight := omegaOne.trans (by linarith only [weightLower, omegaOne])
  have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
  have omegaWeight : changed.omega (receiver.val + 1) ≤ weight := by linarith only [weightLower, omegaOne]
  have locationPositive : 0 < location := changed.location_pos _
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho, rhoAt]; positivity
  have macroInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have rawInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centerInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have envelopeInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).coarserFollowerEnvelope = prepared.coarserFollowerEnvelope := by
    funext index time
    simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have driverInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).weightedMacroSourceState = prepared.weightedMacroSourceState := by
    funext time source
    simp only [CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have remainingInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).followerStrictlyFinerForcing = prepared.followerStrictlyFinerForcing := rfl
  have envelopeData := envelopeEstimate count phase dipoleAngle (prepared.enlargeCap envelopeCapBound) path receiver nonterminal finish finishInside.1
    finishInside.2 (fun current below time inside => (small current below time inside).trans (min_le_left _ _)) weight weightLower
  dsimp only at envelopeData
  simp only [envelopeInvariant, driverInvariant, remainingInvariant] at envelopeData
  obtain ⟨envelopeContinuous, driverContinuous, _, _, _, _, envelopeI, driverI, remainingI, envelopeBound⟩ := envelopeData
  have remainingData := remainingEstimate count phase dipoleAngle (prepared.enlargeCap remainingCapBound) path receiver nonterminal
    path.stop path.stopPositive.le le_rfl entry initialDistance direction entries extents coefficient coefficientPositive magnitude
    (by simpa only [centerInvariant, rawInvariant] using profiles) finish finishInside
    (fun current below time inside => (small current below time inside).trans (min_le_right _ _)) weight omegaWeight rateBounds
  dsimp only at remainingData
  simp only [envelopeInvariant, driverInvariant, remainingInvariant, rawInvariant, centerInvariant] at remainingData
  with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at remainingData
  obtain ⟨_, _, _, _, _, _, _, _, _, remainingBound⟩ := remainingData
  have coarseContinuous : ContinuousOn coarseInput (Icc 0 path.stop) := by
    apply continuousOn_finset_sum
    intro source member
    have below := (Finset.mem_filter.mp member).2
    exact inputContinuous count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source
      (by intro same; subst source; exact (lt_irrefl receiver.val) below)
  have prefixSubset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishInside.2
  have macroIdentity (time : ℝ) : macroValue time = driver time / location ^ 4 := by
    change macroValue time = (location ^ 4 * macroValue time) / location ^ 4
    field_simp [locationPositive.ne']
  have macroContinuous : ContinuousOn macroValue (Icc 0 finish) :=
    (driverContinuous.div_const (location ^ 4)).congr (fun time _ => macroIdentity time)
  have exponential : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have vectorI := (exponential.continuousOn.smul (coarseContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have coarseI := (exponential.continuousOn.mul (coarseContinuous.norm.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have macroI := (exponential.continuousOn.mul macroContinuous).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have coarsePointwise (time : ℝ) (inside : time ∈ Icc 0 finish) :
      ‖coarseInput time‖ ≤ coarseConstant / location ^ 4 * rho * (envelope time + driver time) := by
    have actual := coarseEstimate count phase dipoleAngle (prepared.enlargeCap coarseCapBound) path time (prefixSubset inside) receiver
    dsimp only at actual
    simp only [macroInvariant] at actual
    have mask := General.norm_prefix_with_receiver_nonnegative_le
      (fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source)
      (fun source => mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time source))
      receiver receiver le_rfl
    have maskBound : ‖fun source : Fin count => if source.val ≤ receiver.val then
        changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖ ≤ envelope time + driver time := by
      simpa only [← le_iff_lt_or_eq, ite_true, CascadeSourcePreparedPair.coarserFollowerEnvelope,
        CascadeSourcePreparedPair.weightedMacroSourceState] using mask
    exact actual.trans (mul_le_mul_of_nonneg_left maskBound
      (mul_nonneg (div_nonneg coarseNonnegative (pow_nonneg locationPositive.le 4)) rhoNonnegative))
  have actionBound : weighted (fun time => ‖coarseInput time‖) ≤
      coarseConstant / location ^ 4 * rho * (weighted envelope + weighted driver) := by
    have comparison := intervalIntegral.integral_mono_on finishInside.1 coarseI
      ((envelopeI.add driverI).const_mul (coarseConstant / location ^ 4 * rho)) (by
        intro time inside
        have actual := mul_le_mul_of_nonneg_left (coarsePointwise time inside) (Real.exp_pos (-weight * time)).le
        convert actual using 1; ring)
    simpa only [intervalIntegral.integral_const_mul, intervalIntegral.integral_add envelopeI driverI] using comparison
  have driverIdentity : weighted driver = location ^ 4 * weighted macroValue := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    change Real.exp (-weight * time) * (location ^ 4 * macroValue time) = _
    ring
  change weighted envelope ≤ (2 * responseE / weight) * (rho * weighted driver + weighted remaining) at envelopeBound
  change weighted remaining ≤ 2 * commonBudget + (4 * responseK / weight) * weighted driver at remainingBound
  have closed := coarser_leading_closed_scalar locationPositive weightPositive coarseNonnegative (zero_le_one.trans responseEOne)
    rhoNonnegative actionBound envelopeBound remainingBound driverIdentity
  have numeratorOne : 0 ≤ 2 * responseE * rho := by positivity
  have numeratorTwo : 0 ≤ 8 * responseE * responseK := by positivity
  have quotientOne : 2 * responseE * rho / weight ≤ 2 * responseE * rho :=
    (div_le_iff₀ weightPositive).mpr (le_mul_of_one_le_right numeratorOne weightOne)
  have quotientTwo : 8 * responseE * responseK / weight ^ 2 ≤ 8 * responseE * responseK :=
    (div_le_iff₀ (sq_pos_of_pos weightPositive)).mpr (le_mul_of_one_le_right numeratorTwo (one_le_pow₀ weightOne))
  have coefficientBound : coarseConstant * rho * (1 + 2 * responseE * rho / weight + 8 * responseE * responseK / weight ^ 2) ≤ accuracy :=
    (mul_le_mul_of_nonneg_left (by linarith only [quotientOne, quotientTwo])
      (mul_nonneg coarseNonnegative rhoNonnegative)).trans coefficientSmall.le
  have macroActionNonnegative : 0 ≤ weighted macroValue := intervalIntegral.integral_nonneg finishInside.1
    (fun time _ => mul_nonneg (Real.exp_pos _).le (prepared.macroSourceState_nonnegative time receiver))
  refine ⟨coarseContinuous, macroContinuous, vectorI, coarseI, macroI, ?_⟩
  exact closed.trans (by
    have comparison := mul_le_mul_of_nonneg_right coefficientBound macroActionNonnegative
    linarith only [comparison])

end EulerNonuniqueness.Paper
