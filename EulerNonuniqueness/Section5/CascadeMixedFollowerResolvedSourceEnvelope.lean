import EulerNonuniqueness.Section5.CascadeMixedFollowerOriginalPrefixBudget
import EulerNonuniqueness.Section5.CascadeFollowerResolvedResponse

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_mixed_follower_resolved_source_envelope :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ tolerance : ℝ, 0 < tolerance →
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (2 * responseConstant) ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant : ℝ), 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ drive : Fin count, drive.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, drive.val < source.val →
      let length := changed.length (source.val + 1)
      0 ≤ entry source ∧ entry source ≤ finish ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entry source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion (entry source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
          secondDipoleCenter motion (entry source) source)).re ∧
      ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
        (5 / 4 : ℝ) * length * initialDistance source) →
    (∀ source : Fin count, drive.val < source.val → ∀ time ∈ Icc 0 (entry source),
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
    (∀ source : Fin count, drive.val < source.val → 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
        magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time receiver| + |stableShape motion time receiver| ≤ radius) →
    let envelope := prepared.coarserFollowerEnvelope drive
    let driver := fun time => prepared.weightedMacroSourceState time drive
    let remaining := prepared.followerStrictlyFinerForcing drive
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let rate := responseConstant * changed.omega (drive.val + 1) / changed.ratio +
      responseConstant * rho + responseConstant * tolerance
    let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
    let sourceEnvelope := fun time => ∑ source ∈ finer,
      if time ≤ entry source then
        incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
          (1 + (changed.location (source.val + 1))⁻¹) * magnitude source *
            Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))
      else outgoingConstant * changed.circulation (source.val + 1) *
        (changed.circulation (source.val + 1) * (time - entry source) +
          (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
            ‖centroidAsymmetry motion (entry source) source‖)
    ContinuousOn envelope (Icc 0 finish) ∧ ContinuousOn driver (Icc 0 finish) ∧
    ContinuousOn remaining (Icc 0 finish) ∧ envelope 0 = 0 ∧
    (∀ time ∈ Icc 0 finish, 0 ≤ sourceEnvelope time ∧
      remaining time ≤ sourceEnvelope time + tolerance * envelope time) ∧
    IntervalIntegrable sourceEnvelope volume 0 finish ∧
    ∀ time ∈ Icc 0 finish,
      IntervalIntegrable (fun current => Real.exp (rate * (time - current)) *
        (rho * driver current + sourceEnvelope current)) volume 0 time ∧
      envelope time ≤ responseConstant * ∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * (rho * driver current + sourceEnvelope current) := by
  classical
  obtain ⟨mixedThreshold, mixedPositive, mixedEighth, mixedCap, mixedCapPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, mixedFactory⟩ :=
    exists_uniform_actual_mixed_follower_common_envelope
  obtain ⟨responseThreshold, responsePositive, _, responseCap, responseCapPositive, responseFactory⟩ :=
    exists_uniform_actual_follower_resolved_response
  let rawCap := min mixedCap responseCap
  let thresholdMax := min mixedThreshold responseThreshold
  have capPositive : 0 < rawCap := lt_min mixedCapPositive responseCapPositive
  have capMixed : rawCap ≤ mixedCap := min_le_left _ _
  have capResponse : rawCap ≤ responseCap := min_le_right _ _
  refine ⟨thresholdMax, lt_min mixedPositive responsePositive, (min_le_left _ _).trans mixedEighth,
    rawCap, capPositive, incomingConstant, incomingNonnegative,
    200000 * outgoingConstant, by positivity, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, responses⟩ :=
    responseFactory factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro extent extentOne tolerance tolerancePositive scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant boundaryOne
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [mixedFactory extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans (min_le_left _ _))
      orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    responses scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant boundaryConstant
      (thresholdBound.trans (min_le_right _ _)) referenceNonnegative boundaryOne orbit sectionTime,
    scales.eventually_actual_outgoing_common_envelope_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    eventually_gt_atTop (0 : ℝ)] with frequency mixed response outgoing frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path drive nonterminal finish finishNonnegative finishBound
    entry initialDistance direction
  dsimp only
  intro entries extents coefficient coefficientPositive magnitude profiles small
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  let envelope := prepared.coarserFollowerEnvelope drive
  let driver := fun time => prepared.weightedMacroSourceState time drive
  let remaining := prepared.followerStrictlyFinerForcing drive
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let sigma := constant * changed.omega (drive.val + 1) / changed.ratio + constant * rho
  let rate := sigma + constant * tolerance
  let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
    ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let incoming := fun (source : Fin count) time =>
    incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
      (1 + (changed.location (source.val + 1))⁻¹) * magnitude source *
        Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))
  let later := fun (source : Fin count) time =>
    (200000 * outgoingConstant) * changed.circulation (source.val + 1) *
      (changed.circulation (source.val + 1) * (time - entry source) +
        (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
          ‖centroidAsymmetry motion (entry source) source‖)
  let sourceEnvelope := fun time => ∑ source ∈ finer,
    if time ≤ entry source then incoming source time else later source time
  have macroInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have envelopeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).coarserFollowerEnvelope = prepared.coarserFollowerEnvelope := by
    funext index time
    simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have driverInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).weightedMacroSourceState = prepared.weightedMacroSourceState := by
    funext time source
    simp only [CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have remainingInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).followerStrictlyFinerForcing = prepared.followerStrictlyFinerForcing := rfl
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have gammaNonnegative (source : Fin count) : 0 ≤ changed.circulation (source.val + 1) :=
    (changed.circulation_pos frequencyPositive ratioPositive _).le
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) :
      remaining time ≤ sourceEnvelope time + tolerance * envelope time := by
    let completed := Finset.univ.filter (fun source : Fin count => entry source < time)
    have actual := mixed count phase dipoleAngle (prepared.enlargeCap capMixed) path time
      ⟨inside.1, inside.2.trans finishBound⟩ drive completed entry initialDistance direction
      (fun source done below => by
        have prior := (Finset.mem_filter.mp done).2
        rcases entries source below with ⟨nonnegative, _, large, tiny, unit, first, second, projection, upper⟩
        exact ⟨nonnegative, prior.le, large, tiny, unit, first, second, projection, upper⟩)
      (fun source below notDone => extents source below time ⟨inside.1, le_of_not_gt (by
        simpa only [completed, Finset.mem_filter, Finset.mem_univ, true_and] using notDone)⟩)
    simp only [remainingInvariant, envelopeInvariant, rawInvariant] at actual
    dsimp only [CascadeSourcePreparedPair.enlargeCap] at actual
    have finiteBound : outgoingConstant * (∑ source ∈ finer.filter (fun source => source ∈ completed),
        changed.circulation (source.val + 1) * (4 * ‖centroidAsymmetry motion time source‖ +
          changed.length (source.val + 1) * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
            changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)) +
        incomingConstant * extent ^ 2 * (∑ source ∈ finer.filter (fun source => source ∉ completed),
          changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
            (1 + (changed.location (source.val + 1))⁻¹) * sharpState source time) ≤ sourceEnvelope time := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_ite]
      apply Finset.sum_le_sum
      intro source member
      have below := (Finset.mem_filter.mp member).2
      by_cases done : source ∈ completed
      · have prior := (Finset.mem_filter.mp done).2
        rcases entries source below with ⟨nonnegative, entryBound, large, tiny, unit, first, second, projection, upper⟩
        have actualEnvelope := outgoing count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path source
          (entry source) (finish - entry source) (initialDistance source) nonnegative (sub_nonneg.mpr entryBound)
          (by linarith only [finishBound]) large tiny (direction source) unit first second projection upper
        have elapsed : time - entry source ∈ Icc 0 (finish - entry source) :=
          ⟨(sub_pos.mpr prior).le, sub_le_sub_right inside.2 _⟩
        have affine := actualEnvelope.2 (time - entry source) elapsed
        simp only [show entry source + (time - entry source) = time by ring] at affine
        have initialNonnegative : 0 ≤ initialDistance source := by linarith only [large]
        have extra : changed.length (source.val + 1) ^ 2 ≤
            (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
              ‖centroidAsymmetry motion (entry source) source‖ := by
          nlinarith only [mul_nonneg initialNonnegative (sq_nonneg (changed.length (source.val + 1))),
            norm_nonneg (centroidAsymmetry motion (entry source) source)]
        have delayNonnegative := mul_nonneg (gammaNonnegative source) (sub_nonneg.mpr prior.le)
        have scalar : 4 * ‖centroidAsymmetry motion time source‖ + changed.length (source.val + 1) *
            ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ + changed.radius (source.val + 1) ^ 2 +
              changed.length (source.val + 1) ^ 2 ≤
            200000 * (changed.circulation (source.val + 1) * (time - entry source) +
              (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
                ‖centroidAsymmetry motion (entry source) source‖) := by
          nlinarith only [affine, extra, delayNonnegative, sq_nonneg (changed.length (source.val + 1))]
        have scaled := mul_le_mul_of_nonneg_left scalar (mul_nonneg outgoingNonnegative (gammaNonnegative source))
        simp only [done, ite_true, not_le.mpr prior, ite_false]
        convert scaled using 1 <;> dsimp only [later] <;> ring
      · have laterEntry : time ≤ entry source := le_of_not_gt (by
          simpa only [completed, Finset.mem_filter, Finset.mem_univ, true_and] using done)
        have scaled := mul_le_mul_of_nonneg_left ((profiles source below).2 time ⟨inside.1, laterEntry⟩)
          (show 0 ≤ incomingConstant * extent ^ 2 * (changed.circulation (source.val + 1) *
            changed.length (source.val + 1) ^ 2 * (1 + (changed.location (source.val + 1))⁻¹)) by
            have locationPositive := changed.location_pos (source.val + 1)
            have gamma := gammaNonnegative source
            positivity)
        simp only [done, ite_false, laterEntry, ite_true]
        convert scaled using 1 <;> dsimp only [incoming, sharpState] <;> ring
    exact actual.trans (add_le_add_right finiteBound _)
  have sourceNonnegative (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ sourceEnvelope time := by
    apply Finset.sum_nonneg
    intro source member
    have below := (Finset.mem_filter.mp member).2
    have gamma := gammaNonnegative source
    have locationPositive := changed.location_pos (source.val + 1)
    have magnitudeNonnegative := (profiles source below).1
    have initialNonnegative : 0 ≤ initialDistance source := by linarith only [(entries source below).2.2.1]
    split_ifs with notYet
    · dsimp only [incoming]; positivity
    · have delayNonnegative : 0 ≤ time - entry source := sub_nonneg.mpr (le_of_lt (lt_of_not_ge notYet))
      dsimp only [later]; positivity
  have sourceI : IntervalIntegrable sourceEnvelope volume 0 finish := by
    have single (source : Fin count) : IntervalIntegrable
        (fun time => if time ≤ entry source then incoming source time else later source time) volume 0 finish := by
      have incomingContinuous : Continuous (incoming source) := by dsimp only [incoming]; fun_prop
      have laterContinuous : Continuous (later source) := by dsimp only [later]; fun_prop
      have piecewiseI : Integrable ((Iic (entry source)).piecewise (incoming source) (later source))
          (volume.restrict (uIoc 0 finish)) := Integrable.piecewise measurableSet_Iic
        (incomingContinuous.intervalIntegrable (μ := volume) 0 finish).def'.integrable.integrableOn
        (laterContinuous.intervalIntegrable (μ := volume) 0 finish).def'.integrable.integrableOn
      apply intervalIntegrable_iff.mpr
      simpa only [Set.piecewise, mem_Iic] using piecewiseI
    have finite := IntervalIntegrable.sum (s := finer)
      (f := fun source time => if time ≤ entry source then incoming source time else later source time)
      (fun source _ => single source)
    convert finite using 1
    funext time
    simp only [sourceEnvelope, Finset.sum_apply]
  have responseData := response count phase dipoleAngle (prepared.enlargeCap capResponse) path drive nonterminal
    finish finishNonnegative finishBound small
  dsimp only at responseData
  simp only [envelopeInvariant, driverInvariant, remainingInvariant] at responseData
  obtain ⟨envelopeContinuous, driverContinuous, remainingContinuous, _, _, _, initialZero, _, _, history⟩ := responseData
  let adjusted := fun time => rho * driver time + remaining time - tolerance * envelope time
  have adjustedContinuous : ContinuousOn adjusted (Icc 0 finish) :=
    ((continuousOn_const.mul driverContinuous).add remainingContinuous).sub (continuousOn_const.mul envelopeContinuous)
  have adjustedHistory : ∀ time ∈ Icc 0 finish,
      envelope time ≤ (0 : ℝ) * Real.exp (sigma * time) + constant * ∫ current in (0 : ℝ)..time,
        Real.exp (sigma * (time - current)) * (adjusted current + tolerance * envelope current) := by
    intro time inside
    have actual := (history time inside).2
    have identity : (fun current => Real.exp (sigma * (time - current)) *
        (rho * driver current + remaining current)) = fun current =>
        Real.exp (sigma * (time - current)) * (adjusted current + tolerance * envelope current) := by
      funext current; dsimp only [adjusted]; ring
    rw [identity] at actual
    simpa only [zero_mul, zero_add] using actual
  have resolved := EulerNonuniqueness.exponential_volterra_gronwall envelopeContinuous adjustedContinuous
    tolerancePositive.le (zero_le_one.trans constantOne) finishNonnegative adjustedHistory
  refine ⟨envelopeContinuous, driverContinuous, remainingContinuous, initialZero,
    (fun time inside => ⟨sourceNonnegative time inside, pointwise time inside⟩), sourceI, ?_⟩
  intro time inside
  have subset : uIcc (0 : ℝ) time ⊆ uIcc 0 finish := by
    rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]
    exact Icc_subset_Icc le_rfl inside.2
  have kernelContinuous : Continuous (fun current : ℝ => Real.exp (rate * (time - current))) := by fun_prop
  have sourceKernelI := (sourceI.mono_set subset).mul_continuousOn kernelContinuous.continuousOn
  have driverKernelI : IntervalIntegrable (fun current => Real.exp (rate * (time - current)) *
      (rho * driver current)) volume 0 time := (kernelContinuous.continuousOn.mul
    (continuousOn_const.mul (driverContinuous.mono (Icc_subset_Icc le_rfl inside.2)))).intervalIntegrable_of_Icc (μ := volume) inside.1
  have majorantI := driverKernelI.add sourceKernelI
  have kernelI : IntervalIntegrable (fun current => Real.exp (rate * (time - current)) *
      (rho * driver current + sourceEnvelope current)) volume 0 time := by
    convert majorantI using 1
    funext current; ring
  have adjustedI := (kernelContinuous.continuousOn.mul
    (adjustedContinuous.mono (Icc_subset_Icc le_rfl inside.2))).intervalIntegrable_of_Icc (μ := volume) inside.1
  have comparison := intervalIntegral.integral_mono_on inside.1 adjustedI kernelI (by
    intro current member
    have actual := pointwise current ⟨member.1, member.2.trans inside.2⟩
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    dsimp only [adjusted]
    linarith only [actual])
  refine ⟨kernelI, ?_⟩
  have actual := resolved time inside
  simp only [zero_mul, zero_add] at actual
  exact actual.trans (mul_le_mul_of_nonneg_left comparison (zero_le_one.trans constantOne))

end EulerNonuniqueness.Paper
