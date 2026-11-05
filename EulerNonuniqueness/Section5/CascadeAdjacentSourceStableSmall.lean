import EulerNonuniqueness.Section5.CascadeAdjacentSourceStableEnvelope
import EulerNonuniqueness.Section5.CascadeMacroStateCenteredBound
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity
import EulerNonuniqueness.Section6.SourcePacketBoundedRadiusNeutralSmall
import EulerNonuniqueness.Section1.AdjacentSharpSourcePrefixSeedBudget
import EulerNonuniqueness.Section1.SeedLogarithmicSmallness
import EulerNonuniqueness.General.SwitchedStableConvolution

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_adjacent_source_stable_small :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ coefficient : ℝ, 0 < coefficient →
    ∀ magnitudeMax distanceMax currentMagnitude : ℝ,
    0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 ≤ currentMagnitude →
    ∀ precision : ℝ, 0 < precision →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver drive : Fin count, receiver.val + 1 = drive.val →
    ∀ entry finish initialDistance : ℝ, 0 ≤ entry → entry ≤ finish → finish ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ distanceMax →
    initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (drive.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (drive.val + 1)
    ‖firstDipoleSeparation motion entry drive - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion entry drive - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion entry drive - secondDipoleCenter motion entry drive)).re →
    ‖firstDipoleCenter motion entry drive - secondDipoleCenter motion entry drive‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    (∀ time ∈ Icc 0 entry,
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time drive patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time drive‖ ≤ extent * length) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time drive patch - quadrupoleCenter motion time drive‖ ≤ extent * length)) →
    (∀ time ∈ Icc 0 entry, ∀ patch, motion.domain time drive patch ⊆
      Metric.closedBall (quadrupoleCenter motion time drive) (extent * length)) →
    let sharp := fun source time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    (∀ time ∈ Icc 0 entry, sharp drive time ≤ magnitudeMax *
      Real.exp (coefficient * changed.omega (drive.val + 1) * (time - entry))) →
    let lambda := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let seed := changed.seed (receiver.val + 1)
    (∀ time ∈ Icc 0 finish, sharp receiver time ≤ currentMagnitude * seed * Real.exp (lambda * (time - entry))) →
    seed * Real.exp (lambda * (finish - entry)) ≤ 1 →
    let input := relativeBlockSourceShapeInput changed motion prepared.reference receiver drive
    let kernel := fun time => Real.exp (-(lambda / 2) * (finish - time))
    ContinuousOn input (Icc 0 finish) ∧
    IntervalIntegrable (fun time => kernel time * ‖input time‖) volume 0 finish ∧
    IntervalIntegrable (fun time => kernel time * |(input time).2|) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, kernel time * ‖input time‖) ≤ precision ∧
    (∫ time in (0 : ℝ)..finish, kernel time * |(input time).2|) ≤ precision := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, envelopeCap, envelopePositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, envelopes⟩ :=
    exists_uniform_actual_adjacent_source_stable_envelope
  obtain ⟨continuityCap, continuityPositive, states⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min envelopeCap continuityCap
  have capPositive : 0 < rawCap := lt_min envelopePositive continuityPositive
  have envelopeCapBound : rawCap ≤ envelopeCap := min_le_left _ _
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro extent extentOne coefficient coefficientPositive magnitudeMax distanceMax currentMagnitude magnitudeNonnegative
    distanceNonnegative currentNonnegative precision precisionPositive scales amplitudePositive ratioBound alphaPositive
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot
    boundaryConstant factorPositive factorSmall rootOne boundaryOne
  let accuracy := precision / (16 * (1 + currentMagnitude))
  have accuracyPositive : 0 < accuracy := by dsimp only [accuracy]; positivity
  let constant := 4 * outgoingConstant + 100 *
    (incomingConstant * extent ^ 2 * magnitudeMax / coefficient + outgoingConstant * (2 + distanceMax))
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  let small := precision / (8 * (1 + constant))
  have smallPositive : 0 < small := by dsimp only [small]; positivity
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  filter_upwards [envelopes extent extentOne accuracy accuracyPositive scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot
      boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_bounded_radius_source_neutral_small amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne) (zero_lt_one.trans_le extentOne) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans thresholdEighth) referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    scales.eventually_seed_logarithmic_small ratioBound alphaPositive smallPositive,
    scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive 0 (by norm_num : (0 : ℝ) < 1) smallPositive,
    eventually_ge_atTop (1 : ℝ)] with frequency envelope neutral inputs lengths logarithmic seeds frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver drive adjacent entry finish initialDistance
    entryNonnegative entryBefore finishBound initialLarge distanceBound initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper extents domains driverProfile currentProfile exposure
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (receiver.val + 1)
  let lambda := 2 * Real.sqrt 2 * omega
  let gamma := lambda / 2
  let seed := changed.seed (receiver.val + 1)
  let input := relativeBlockSourceShapeInput changed motion prepared.reference receiver drive
  let receiverMacro := fun time => prepared.macroSourceState time receiver
  let beta := coefficient * changed.omega (drive.val + 1)
  let incoming := incomingConstant * extent ^ 2 * (changed.circulation (drive.val + 1) * changed.length (drive.val + 1) ^ 2 /
    |changed.location (receiver.val + 1) - changed.location (drive.val + 1)| ^ 4 *
      (1 + changed.location (receiver.val + 1) / changed.location (drive.val + 1)) * magnitudeMax)
  let slope := outgoingConstant / changed.location (receiver.val + 1) ^ 4 * changed.circulation (drive.val + 1) ^ 2
  let offset := outgoingConstant / changed.location (receiver.val + 1) ^ 4 * changed.circulation (drive.val + 1) *
    ((1 + initialDistance) * changed.length (drive.val + 1) ^ 2 + ‖centroidAsymmetry motion entry drive‖)
  have finishNonnegative : 0 ≤ finish := entryNonnegative.trans entryBefore
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have gammaLower : omega ≤ gamma := by
    have sqrtLower : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    dsimp only [gamma, lambda]
    nlinarith only [mul_le_mul_of_nonneg_right sqrtLower omegaPositive.le]
  have gammaPositive : 0 < gamma := omegaPositive.trans_le gammaLower
  have lambdaLower : omega ≤ lambda := by dsimp only [gamma] at gammaLower; linarith only [gammaLower, omegaPositive]
  have betaPositive : 0 < beta := mul_pos coefficientPositive (changed.omega_pos frequencyPositive ratioPositive _)
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have sourceGamma := (changed.circulation_pos frequencyPositive ratioPositive (drive.val + 1)).le
  have initialNonnegative : 0 ≤ initialDistance := by linarith only [initialLarge]
  have receiverLocationPositive := changed.location_pos (receiver.val + 1)
  have driverLocationPositive := changed.location_pos (drive.val + 1)
  have incomingNonneg : 0 ≤ incoming := by dsimp only [incoming]; positivity
  have slopeNonneg : 0 ≤ slope := by dsimp only [slope]; positivity
  have offsetNonneg : 0 ≤ offset := by dsimp only [offset]; positivity
  have inputContinuous : ContinuousOn input (Icc 0 finish) :=
    (inputs count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver drive (by intro equal; simp only [equal] at adjacent; omega)).mono
      (Icc_subset_Icc le_rfl finishBound)
  have macroContinuous : ContinuousOn receiverMacro (Icc 0 finish) :=
    (states prepared capPositive (min_le_right _ _) path receiver).2.2.2.mono (Icc_subset_Icc le_rfl finishBound)
  have rawInvariant : (prepared.enlargeCap envelopeCapBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant : (prepared.enlargeCap envelopeCapBound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have macroInvariant : (prepared.enlargeCap envelopeCapBound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have envelopeAt (time : ℝ) (inside : time ∈ Icc 0 finish) : ‖input time‖ ≤
      (if time ≤ entry then incoming * Real.exp (beta * (time - entry)) else slope * (time - entry) + offset) + accuracy * receiverMacro time := by
    have actual := envelope count phase dipoleAngle (prepared.enlargeCap envelopeCapBound) path receiver drive (by omega)
      finish finishNonnegative finishBound (fun _ => entry) (fun _ => initialDistance) (fun _ => direction)
      (by intro source member; have equal := Finset.mem_singleton.mp member; subst source
          exact ⟨entryNonnegative, entryBefore, initialLarge, initialSmall, directionNorm, firstInitial, secondInitial, initialProjection, initialUpper⟩)
      (by intro source member; have equal := Finset.mem_singleton.mp member; subst source; exact extents)
      coefficient coefficientPositive (fun _ => magnitudeMax)
    dsimp only at actual
    simp only [rawInvariant, centeredInvariant, macroInvariant] at actual
    dsimp only [CascadeSourcePreparedPair.enlargeCap] at actual
    have profile : ∀ source ∈ ({drive} : Finset (Fin count)), 0 ≤ magnitudeMax ∧
        ∀ time ∈ Icc 0 entry,
          prepared.rawSourceCenteredState time source +
            ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
            ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch ≤
              magnitudeMax * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry)) := by
      intro source member
      have equal := Finset.mem_singleton.mp member
      subst source
      exact ⟨magnitudeNonnegative, driverProfile⟩
    exact (actual profile time inside).1
  have kernel : Continuous (fun time : ℝ => Real.exp (-gamma * (finish - time))) := by fun_prop
  have normI := (kernel.continuousOn.mul inputContinuous.norm).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have scalarI := (kernel.continuousOn.mul inputContinuous.snd.abs).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have macroI := (kernel.continuousOn.mul macroContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have switched := EulerNonuniqueness.General.switched_stable_convolution_bound entryNonnegative entryBefore gammaPositive
    (add_pos betaPositive gammaPositive) incomingNonneg slopeNonneg offsetNonneg
    (inputContinuous.norm.sub ((continuousOn_const (c := accuracy)).mul macroContinuous))
    (fun time inside => by have bound := envelopeAt time ⟨inside.1, inside.2.trans entryBefore⟩; rw [if_pos inside.2] at bound; linarith only [bound])
    (fun time inside => by have bound := envelopeAt time ⟨entryNonnegative.trans inside.1.le, inside.2⟩; rw [if_neg (not_le.mpr inside.1)] at bound; linarith only [bound])
  have neutralBound := neutral prepared.toCascadeMaterialPreparedPair path
    (thresholdBound.trans (thresholdEighth.trans (by norm_num))) (factorSmall.trans (by norm_num)) drive entry entryNonnegative
    (entryBefore.trans finishBound) domains entry ⟨entryNonnegative, le_rfl⟩
  have normalized := changed.adjacent_sharp_source_prefix_seed_budget_le frequencyPositive ratioPositive
    (incoming := incomingConstant) (outgoing := outgoingConstant) (extent := extent) (magnitude := magnitudeMax)
    (distance := initialDistance) (neutralFactor := 1) (coefficient := coefficient) (weight := omega)
    (neutral := ‖centroidAsymmetry motion entry drive‖)
    incomingNonnegative outgoingNonnegative (zero_le_one.trans extentOne) magnitudeNonnegative initialNonnegative
    (by norm_num : (0 : ℝ) ≤ 1) coefficientPositive (receiver.val + 1) le_rfl
    (norm_nonneg (centroidAsymmetry motion entry drive))
    (by simpa only [show receiver.val + 1 + 1 = drive.val + 1 by omega] using neutralBound)
  rw [show receiver.val + 1 + 1 = drive.val + 1 by omega] at normalized
  have normalization : incoming / beta + slope / omega ^ 2 + offset / omega ≤ constant * seed := by
    have ratioSquare : 1 ≤ changed.ratio ^ 2 := one_le_pow₀ (by change 1 ≤ scales.ratio; linarith only [ratioBound])
    have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
    have incomingCompare := div_le_div_of_nonneg_left (by positivity : 0 ≤ incomingConstant * extent ^ 2 * magnitudeMax)
      coefficientPositive (le_mul_of_one_le_right coefficientPositive.le ratioSquare)
    have outgoingCompare := div_le_self (by positivity : 0 ≤ outgoingConstant * (1 + initialDistance + 1)) ratioOne
    have distanceCompare := mul_le_mul_of_nonneg_left (by linarith only [distanceBound] : 1 + initialDistance + 1 ≤ 2 + distanceMax) outgoingNonnegative
    have coefficientCompare : 4 * outgoingConstant + 100 *
        (incomingConstant * extent ^ 2 * magnitudeMax / (coefficient * changed.ratio ^ 2) +
          outgoingConstant * (1 + initialDistance + 1) / changed.ratio) ≤ constant := by
      dsimp only [constant]; linarith only [incomingCompare, outgoingCompare, distanceCompare]
    have actual := normalized.trans (mul_le_mul_of_nonneg_right coefficientCompare seedPositive.le)
    convert actual using 1
    dsimp only [incoming, beta, slope, offset, omega, seed]
    ring
  obtain ⟨_, seedOne, logSmall⟩ := logarithmic (receiver.val + 1)
  have seedSmall : seed < small := by simpa only [pow_zero, one_mul, Real.rpow_one] using seeds (receiver.val + 1)
  have ageNonnegative : 0 ≤ finish - entry := sub_nonneg.mpr entryBefore
  have ageBound : omega * (finish - entry) ≤ Real.log (seed⁻¹) := by
    have logged := Real.log_le_log (mul_pos seedPositive (Real.exp_pos _)) exposure
    rw [Real.log_mul seedPositive.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_one] at logged
    change Real.log seed + lambda * (finish - entry) ≤ 0 at logged
    have faster := mul_le_mul_of_nonneg_right lambdaLower ageNonnegative
    rw [Real.log_inv]
    linarith only [logged, faster]
  have budgetPositive : 0 ≤ incoming / beta + slope / omega ^ 2 + offset / omega := by positivity
  have switchedSmall : incoming / (beta + gamma) * Real.exp (-gamma * (finish - entry)) +
      (slope * (finish - entry) + offset) / gamma ≤ precision / 2 := by
    have exponential : Real.exp (-gamma * (finish - entry)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [gammaPositive, ageNonnegative])
    have incomingBound := (mul_le_mul_of_nonneg_left exponential (div_nonneg incomingNonneg (add_pos betaPositive gammaPositive).le)).trans
      (by simpa only [mul_one] using div_le_div_of_nonneg_left incomingNonneg betaPositive (le_add_of_nonneg_right gammaPositive.le))
    have outgoingBound := div_le_div_of_nonneg_left (by positivity : 0 ≤ slope * (finish - entry) + offset) omegaPositive gammaLower
    have algebra : incoming / beta + (slope * (finish - entry) + offset) / omega ≤
        (incoming / beta + slope / omega ^ 2 + offset / omega) * (1 + omega * (finish - entry)) := by
      apply le_of_sub_nonneg
      have identity : (incoming / beta + slope / omega ^ 2 + offset / omega) * (1 + omega * (finish - entry)) -
          (incoming / beta + (slope * (finish - entry) + offset) / omega) =
          slope / omega ^ 2 + (incoming / beta + offset / omega) * (omega * (finish - entry)) := by
        field_simp
        ring
      rw [identity]
      positivity
    have combined := (add_le_add incomingBound outgoingBound).trans algebra
    have enlarged := mul_le_mul_of_nonneg_right normalization (by positivity : 0 ≤ 1 + omega * (finish - entry))
    have aged := mul_le_mul_of_nonneg_left ageBound (mul_nonneg constantNonnegative seedPositive.le)
    have smallSeed := mul_le_mul_of_nonneg_left seedSmall.le constantNonnegative
    have smallLog := mul_le_mul_of_nonneg_left logSmall.le constantNonnegative
    change constant * (seed * Real.log (seed⁻¹)) ≤ constant * small at smallLog
    have target : constant * seed * (1 + omega * (finish - entry)) ≤ precision / 2 := by
      have constantBound : constant * small ≤ precision / 8 := by
        dsimp only [small]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < 8 * (1 + constant))).mpr
        nlinarith only [precisionPositive]
      calc
        _ = constant * seed + constant * seed * (omega * (finish - entry)) := by ring
        _ ≤ constant * small + constant * small :=
          add_le_add smallSeed (aged.trans (by simpa only [mul_assoc] using smallLog))
        _ ≤ precision / 2 := by linarith only [constantBound, precisionPositive]
    exact combined.trans (enlarged.trans target)
  have macroBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      receiverMacro time ≤ 4 * currentMagnitude * seed * Real.exp (lambda * (time - entry)) := by
    have actual := prepared.macroSourceState_le_centered_and_raw path ⟨inside.1, inside.2.trans finishBound⟩ receiver
    rw [← prepared.referenceIdentity, norm_sub_rev] at actual
    have lengthRatio : changed.length (receiver.val + 1) / changed.location (receiver.val + 1) ≤ 1 :=
      (div_le_one (changed.location_pos _)).mpr (by simpa only [one_mul] using (lengths (receiver.val + 1)).le)
    have centeredNonnegative : 0 ≤ prepared.rawSourceCenteredState time receiver := div_nonneg (norm_nonneg _) (changed.length_pos _).le
    have rawNonnegative : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch := by
      apply Finset.sum_nonneg; intro patch _; dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
    have centerNonnegative := div_nonneg (norm_nonneg (quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver)) (changed.location_pos (receiver.val + 1)).le
    have momentNonnegative := norm_nonneg (relativeNormalizedFirstMoment changed motion prepared.reference receiver time)
    have centeredScaled := mul_le_mul_of_nonneg_right lengthRatio (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) centeredNonnegative)
    have sharp := currentProfile time inside
    nlinarith only [actual, centeredScaled, sharp, rawNonnegative, centerNonnegative, momentNonnegative]
  have weightedMacroI := (((by fun_prop : Continuous (fun time : ℝ => Real.exp (-(-gamma) * time)))).continuousOn.mul macroContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have faster := intervalIntegral.exp_mul_integral_le_of_faster_exponential_majorant finishNonnegative
    (show -gamma < lambda by linarith only [gammaPositive, lambdaLower, omegaPositive])
    (show 0 ≤ 4 * currentMagnitude * seed by positivity) weightedMacroI macroBound
  have macroKernel : (∫ time in (0 : ℝ)..finish, Real.exp (-gamma * (finish - time)) * receiverMacro time) ≤ 4 * currentMagnitude := by
    have identity : (∫ time in (0 : ℝ)..finish, Real.exp (-gamma * (finish - time)) * receiverMacro time) =
        Real.exp (-gamma * finish) * ∫ time in (0 : ℝ)..finish, Real.exp (-(-gamma) * time) * receiverMacro time := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr; intro time _
      dsimp only
      rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [identity]
    have first : Real.exp (-gamma * finish) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-(-gamma) * time) * receiverMacro time) ≤
        (4 * currentMagnitude / (lambda + gamma)) * (seed * Real.exp (lambda * (finish - entry))) := by
      convert faster using 1
      ring
    have second := mul_le_mul_of_nonneg_left exposure (by positivity : 0 ≤ 4 * currentMagnitude / (lambda + gamma))
    have denominator : 1 ≤ lambda + gamma := by linarith only [omegaOne, lambdaLower, gammaPositive]
    exact first.trans (second.trans (by simpa only [mul_one] using div_le_self (by positivity : 0 ≤ 4 * currentMagnitude) denominator))
  have feedbackSmall : accuracy * (∫ time in (0 : ℝ)..finish, Real.exp (-gamma * (finish - time)) * receiverMacro time) ≤ precision / 2 := by
    apply (mul_le_mul_of_nonneg_left macroKernel accuracyPositive.le).trans
    dsimp only [accuracy]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 16 * (1 + currentMagnitude))).mpr
    nlinarith only [precisionPositive, currentNonnegative, mul_nonneg precisionPositive.le currentNonnegative]
  have subtractionIdentity : (∫ time in (0 : ℝ)..finish,
      Real.exp (-gamma * (finish - time)) * (‖input time‖ - accuracy * receiverMacro time)) =
      (∫ time in (0 : ℝ)..finish, Real.exp (-gamma * (finish - time)) * ‖input time‖) -
        accuracy * (∫ time in (0 : ℝ)..finish, Real.exp (-gamma * (finish - time)) * receiverMacro time) := by
    have pointwise (time : ℝ) : Real.exp (-gamma * (finish - time)) * (‖input time‖ - accuracy * receiverMacro time) =
        Real.exp (-gamma * (finish - time)) * ‖input time‖ - accuracy * (Real.exp (-gamma * (finish - time)) * receiverMacro time) := by ring
    simp_rw [pointwise]
    rw [intervalIntegral.integral_sub normI (macroI.const_mul accuracy), intervalIntegral.integral_const_mul]
  rw [subtractionIdentity] at switched
  have normSmall : (∫ time in (0 : ℝ)..finish, Real.exp (-gamma * (finish - time)) * ‖input time‖) ≤ precision := by
    linarith only [switched, switchedSmall, feedbackSmall]
  refine ⟨inputContinuous, normI, scalarI, normSmall, ?_⟩
  apply (intervalIntegral.integral_mono_on finishNonnegative scalarI normI ?_).trans normSmall
  intro time _
  exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_snd_le (input time)) (Real.exp_pos _).le

end EulerNonuniqueness.Paper
