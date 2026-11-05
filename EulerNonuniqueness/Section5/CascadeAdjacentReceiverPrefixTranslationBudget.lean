import EulerNonuniqueness.Section5.CascadeMixedFollowerResolvedSourceEnvelope
import EulerNonuniqueness.Section5.CascadeMacroStateCenteredBound
import EulerNonuniqueness.General.TwoRateExponentialResponse

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem affine_le_exponential {slope constant rate time : ℝ}
    (slopeNonnegative : 0 ≤ slope) (constantNonnegative : 0 ≤ constant)
    (ratePositive : 0 < rate) (timeNonnegative : 0 ≤ time) :
    slope * time + constant ≤ (slope / rate + constant) * Real.exp (rate * time) := by
  have timeBound : time ≤ Real.exp (rate * time) / rate := by
    apply (le_div_iff₀ ratePositive).mpr
    have exponential := Real.add_one_le_exp (rate * time)
    nlinarith only [exponential]
  have exponentialOne : 1 ≤ Real.exp (rate * time) :=
    Real.one_le_exp_iff.mpr (mul_nonneg ratePositive.le timeNonnegative)
  have first := mul_le_mul_of_nonneg_left timeBound slopeNonnegative
  have second := le_mul_of_one_le_right constantNonnegative exponentialOne
  (convert add_le_add first second using 1; ring)

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_adjacent_receiver_prefix_translation_budget :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ coefficient : ℝ, 0 < coefficient →
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max (max 2 (2 * responseConstant))
      (max (4 * responseConstant / coefficient) (4 * Real.sqrt 2 / coefficient)) ≤ scales.ratio →
    0 < scales.alpha → ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude →
    ∀ threshold ≤ thresholdMax, ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant : ℝ),
    1 ≤ boundaryConstant → ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver drive : Fin count, receiver.val + 1 = drive.val → drive.val + 1 < count →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
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
    ∀ magnitude : Fin count → ℝ, ∀ driverMagnitude ≥ (0 : ℝ),
    let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    (∀ source : Fin count, drive.val < source.val → 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
        magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    (∀ time ∈ Icc 0 finish, sharpState drive time ≤ driverMagnitude *
      Real.exp (coefficient * changed.omega (drive.val + 1) * (time - finish))) →
    (∀ current : Fin count, current.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time current| + |stableShape motion time current| ≤ radius) →
    let nu := coefficient * changed.omega (drive.val + 1)
    let lambda := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let rate := responseConstant * changed.omega (drive.val + 1) / changed.ratio +
      responseConstant * rho + responseConstant * (coefficient / (8 * responseConstant))
    let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
    let sourceBudget := ∑ source ∈ finer,
      (incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
        (1 + (changed.location (source.val + 1))⁻¹) * magnitude source +
      outgoingConstant * changed.circulation (source.val + 1) *
        (changed.circulation (source.val + 1) / nu + (1 + initialDistance source) *
          changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry source) source‖)) *
        Real.exp (nu * (finish - entry source))
    let totalBudget := 4 * rho * changed.location (drive.val + 1) ^ 4 * driverMagnitude + sourceBudget
    let translation := fun time => ‖quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver‖ /
      changed.location (receiver.val + 1)
    0 < nu ∧ rate ≤ nu / 2 ∧ lambda ≤ nu / 2 ∧ ContinuousOn translation (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-lambda * time) * translation time) volume 0 finish ∧
    Real.exp (lambda * finish) * (∫ time in (0 : ℝ)..finish, Real.exp (-lambda * time) * translation time) ≤
      responseConstant * totalBudget / (changed.location (receiver.val + 1) ^ 4 * (nu - rate) * (nu - lambda)) ∧
    Real.exp (lambda * finish) * (∫ time in (0 : ℝ)..finish, Real.exp (-lambda * time) * translation time) ≤
      4 * responseConstant * totalBudget / (changed.location (receiver.val + 1) ^ 4 * nu ^ 2) := by
  classical
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, incomingConstant, incomingNonnegative,
    outgoingConstant, outgoingNonnegative, factories⟩ := exists_uniform_actual_mixed_follower_resolved_source_envelope
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, factory⟩ := factories factor factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro extent extentOne coefficient coefficientPositive scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant boundaryOne
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantOne
  have responseRatio : max 2 (2 * constant) ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans responseRatio
  have feedbackDecay := (((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
    ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)).const_mul constant
  simp only [mul_zero, zero_add] at feedbackDecay
  have tolerancePositive : 0 < coefficient / (8 * constant) := by positivity
  filter_upwards [factory extent extentOne (coefficient / (8 * constant)) tolerancePositive scales scaleRoot rootLarge
      amplitudeIdentity responseRatio alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
      orbit sectionTime boundaryConstant boundaryOne,
    feedbackDecay.eventually (eventually_lt_nhds (div_pos coefficientPositive (by norm_num : (0 : ℝ) < 8))),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)] with frequency estimates feedbackSmall lengths frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver drive adjacent nonterminal finish finishNonnegative finishBound
    entry initialDistance direction
  dsimp only
  intro entries extents magnitude driverMagnitude driverNonnegative profiles driverProfile small
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (drive.val + 1)
  let nu := coefficient * omega
  let lambda := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let rate := constant * omega / changed.ratio + constant * rho + constant * (coefficient / (8 * constant))
  let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  let incoming := fun source : Fin count => incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) *
    changed.length (source.val + 1) ^ 2 * (1 + (changed.location (source.val + 1))⁻¹) * magnitude source
  let base := fun source : Fin count => (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
    ‖centroidAsymmetry motion (entry source) source‖
  let later := fun source : Fin count => outgoingConstant * changed.circulation (source.val + 1) *
    (changed.circulation (source.val + 1) / nu + (1 + initialDistance source) *
      changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry source) source‖)
  let sourceBudget := ∑ source ∈ finer, (incoming source + later source) * Real.exp (nu * (finish - entry source))
  let totalBudget := 4 * rho * changed.location (drive.val + 1) ^ 4 * driverMagnitude + sourceBudget
  let envelope := prepared.coarserFollowerEnvelope drive
  let driver := fun time => prepared.weightedMacroSourceState time drive
  let translation := fun time => ‖quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver‖ /
    changed.location (receiver.val + 1)
  let sourceEnvelope := fun time => ∑ source ∈ finer, if time ≤ entry source then incoming source *
    Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source)) else
    outgoingConstant * changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) * (time - entry source) +
      (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry source) source‖)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
  have ratioPositive : 0 < changed.ratio := zero_lt_one.trans_le ratioOne
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive ratioOne _)
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have nuPositive : 0 < nu := mul_pos coefficientPositive omegaPositive
  have receiverLocationPositive := changed.location_pos (receiver.val + 1)
  have gammaNonnegative (source : Fin count) : 0 ≤ changed.circulation (source.val + 1) :=
    (changed.circulation_pos frequencyPositive ratioPositive _).le
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive (source + 1)).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive (source + 1)).le (pow_nonneg (changed.location_pos _).le _)
    exact add_nonneg (mul_nonneg (by norm_num) hessianNonnegative) (mul_nonneg (by norm_num) strainNonnegative)
  have rateHalf : rate ≤ nu / 2 := by
    have ratioFeedback : 4 * constant / coefficient ≤ changed.ratio :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge)
    have scaled := (div_le_iff₀ coefficientPositive).mp ratioFeedback
    have first : constant * omega / changed.ratio ≤ nu / 4 := by
      apply (div_le_iff₀ ratioPositive).mpr
      dsimp only [nu]
      nlinarith only [mul_le_mul_of_nonneg_right scaled omegaPositive.le]
    have toleranceIdentity : constant * (coefficient / (8 * constant)) = coefficient / 8 := by field_simp; ring
    have coefficientOmega := mul_le_mul_of_nonneg_left omegaOne coefficientPositive.le
    simp only [mul_one] at coefficientOmega
    change constant * rho < coefficient / 8 at feedbackSmall
    dsimp only [rate]
    rw [toleranceIdentity]
    change coefficient ≤ nu at coefficientOmega
    linarith only [first, feedbackSmall, coefficientOmega]
  have adjacentOmega : omega = changed.omega (receiver.val + 1) * changed.ratio := by
    dsimp only [omega]
    rw [← adjacent]
    simp only [Scales.omega, pow_succ]
    ring
  have lambdaHalf : lambda ≤ nu / 2 := by
    have ratioLambda : 4 * Real.sqrt 2 / coefficient ≤ changed.ratio :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge)
    have scaled := (div_le_iff₀ coefficientPositive).mp ratioLambda
    have receiverPositive := changed.omega_pos frequencyPositive ratioPositive (receiver.val + 1)
    dsimp only [lambda, nu]
    rw [adjacentOmega]
    nlinarith only [mul_le_mul_of_nonneg_right scaled receiverPositive.le]
  have incomingNonnegativeSource (source : Fin count) (member : source ∈ finer) : 0 ≤ incoming source := by
    have magnitudeNonnegative := (profiles source (Finset.mem_filter.mp member).2).1
    have locationPositive := changed.location_pos (source.val + 1)
    have gamma := gammaNonnegative source
    dsimp only [incoming]; positivity
  have baseNonnegative (source : Fin count) (member : source ∈ finer) : 0 ≤ base source := by
    have initialNonnegative : 0 ≤ initialDistance source := by linarith only [(entries source (Finset.mem_filter.mp member).2).2.2.1]
    dsimp only [base]; positivity
  have laterNonnegative (source : Fin count) (member : source ∈ finer) : 0 ≤ later source := by
    have gamma := gammaNonnegative source
    have basePositive := baseNonnegative source member
    have quotient := div_nonneg gamma nuPositive.le
    have valuePositive : 0 ≤ changed.circulation (source.val + 1) / nu + (1 + initialDistance source) *
        changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry source) source‖ := by
      dsimp only [base] at basePositive
      linarith only [quotient, basePositive]
    exact mul_nonneg (mul_nonneg outgoingNonnegative gamma) valuePositive
  have sourceNonnegative : 0 ≤ sourceBudget := Finset.sum_nonneg fun source member =>
    mul_nonneg (add_nonneg (incomingNonnegativeSource source member) (laterNonnegative source member)) (Real.exp_pos _).le
  have totalNonnegative : 0 ≤ totalBudget := by dsimp only [totalBudget]; positivity
  have sourceProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      sourceEnvelope time ≤ sourceBudget * Real.exp (nu * (time - finish)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro source member
    have exponent : Real.exp (nu * (finish - entry source)) * Real.exp (nu * (time - finish)) =
        Real.exp (nu * (time - entry source)) := by rw [← Real.exp_add]; congr 1; ring
    conv_rhs => rw [mul_assoc, exponent]
    have below := (Finset.mem_filter.mp member).2
    by_cases before : time ≤ entry source
    · have omegaOrder : omega ≤ changed.omega (source.val + 1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ ratioOne (by omega : drive.val + 1 ≤ source.val + 1)) frequencyPositive.le
      have rateOrder := mul_le_mul_of_nonneg_left omegaOrder coefficientPositive.le
      have expOrder := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right rateOrder (sub_nonpos.mpr before))
      simp only [before, ite_true]
      exact (mul_le_mul_of_nonneg_left expOrder (incomingNonnegativeSource source member)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (laterNonnegative source member)) (Real.exp_pos _).le)
    · have affine := affine_le_exponential (gammaNonnegative source) (baseNonnegative source member) nuPositive
        (sub_nonneg.mpr (le_of_lt (lt_of_not_ge before)))
      have scaled := mul_le_mul_of_nonneg_left affine (mul_nonneg outgoingNonnegative (gammaNonnegative source))
      simp only [before, ite_false]
      have increase : later source * Real.exp (nu * (time - entry source)) ≤
          (incoming source + later source) * Real.exp (nu * (time - entry source)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (incomingNonnegativeSource source member))
        (Real.exp_pos (nu * (time - entry source))).le
      apply le_trans ?_ increase
      convert scaled using 1 <;> dsimp only [later, base] <;> ring
  have driverProfile' (time : ℝ) (inside : time ∈ Icc 0 finish) :
      driver time ≤ 4 * changed.location (drive.val + 1) ^ 4 * driverMagnitude * Real.exp (nu * (time - finish)) := by
    have actual := prepared.macroSourceState_le_centered_and_raw path ⟨inside.1, inside.2.trans finishBound⟩ drive
    rw [← prepared.referenceIdentity, norm_sub_rev] at actual
    have lengthRatio : changed.length (drive.val + 1) / changed.location (drive.val + 1) ≤ 1 :=
      (div_le_one (changed.location_pos _)).mpr (by simpa only [one_mul] using (lengths (drive.val + 1)).le)
    have centeredNonnegative : 0 ≤ prepared.rawSourceCenteredState time drive :=
      div_nonneg (norm_nonneg _) (changed.length_pos _).le
    have rawNonnegative : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget time drive patch := by
      apply Finset.sum_nonneg; intro patch _; dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
    have centerNonnegative := div_nonneg (norm_nonneg (quadrupoleCenter motion time drive - quadrupoleCenter prepared.reference time drive)) (changed.location_pos (drive.val + 1)).le
    have momentNonnegative := norm_nonneg (relativeNormalizedFirstMoment changed motion prepared.reference drive time)
    have centeredScaled := mul_le_mul_of_nonneg_right lengthRatio
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) centeredNonnegative)
    have sharp := driverProfile time inside
    have macroBound : prepared.macroSourceState time drive ≤ 4 * driverMagnitude * Real.exp (nu * (time - finish)) := by
      nlinarith only [actual, centeredScaled, sharp, rawNonnegative, centerNonnegative, momentNonnegative]
    have scaled := mul_le_mul_of_nonneg_left macroBound (pow_nonneg (changed.location_pos (drive.val + 1)).le 4)
    (convert scaled using 1; dsimp only [driver, CascadeSourcePreparedPair.weightedMacroSourceState]; ring)
  have data := estimates count phase dipoleAngle prepared path drive nonterminal finish finishNonnegative finishBound
    entry initialDistance direction entries extents coefficient coefficientPositive magnitude profiles small
  dsimp only at data
  obtain ⟨envelopeContinuous, driverContinuous, remainingContinuous, initialZero, pointwise, sourceI, response⟩ := data
  change ContinuousOn envelope (Icc 0 finish) at envelopeContinuous
  change ContinuousOn driver (Icc 0 finish) at driverContinuous
  change IntervalIntegrable sourceEnvelope volume 0 finish at sourceI
  change ∀ time ∈ Icc 0 finish, IntervalIntegrable (fun current => Real.exp (rate * (time - current)) *
    (rho * driver current + sourceEnvelope current)) volume 0 time ∧ envelope time ≤ constant *
      ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * (rho * driver current + sourceEnvelope current) at response
  have rateLess : rate < nu := rateHalf.trans_lt (half_lt_self nuPositive)
  have gapPositive : 0 < nu - rate := sub_pos.mpr rateLess
  have envelopeProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      envelope time ≤ constant * totalBudget / (nu - rate) * Real.exp (nu * (time - finish)) := by
    have prefixSubset : uIcc (0 : ℝ) time ⊆ uIcc 0 finish := by
      rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]; exact Icc_subset_Icc le_rfl inside.2
    have forcingI := ((driverContinuous.mono (Icc_subset_Icc le_rfl inside.2)).intervalIntegrable_of_Icc (μ := volume) inside.1).const_mul rho
    have weightedI := (forcingI.add (sourceI.mono_set prefixSubset)).continuousOn_mul
      (show ContinuousOn (fun current : ℝ => Real.exp (-rate * current)) (uIcc 0 time) by fun_prop)
    have comparison := intervalIntegral.exp_mul_integral_le_of_faster_exponential_majorant inside.1 rateLess
      totalNonnegative weightedI (fun current member => by
        have sourceBound := sourceProfile current ⟨member.1, member.2.trans inside.2⟩
        have driverBound := mul_le_mul_of_nonneg_left (driverProfile' current ⟨member.1, member.2.trans inside.2⟩) rhoNonnegative
        (convert add_le_add driverBound sourceBound using 1; dsimp only [totalBudget]; ring))
    have actual := (response time inside).2
    have identity : (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
        (rho * driver current + sourceEnvelope current)) = Real.exp (rate * time) *
        ∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * (rho * driver current + sourceEnvelope current) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr; intro current _
      dsimp only
      rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
    rw [identity] at actual
    exact actual.trans (by convert mul_le_mul_of_nonneg_left comparison constantPositive.le using 1; ring)
  have referenceContinuous : Continuous (fun time => quadrupoleCenter prepared.reference time receiver) := by
    rw [prepared.referenceIdentity]; exact prepared.referenceWitness.trajectory.movingFamily.quadrupoleCenter_continuous receiver
  have translationContinuous : Continuous translation :=
    (((prepared.trajectory.movingFamily.quadrupoleCenter_continuous receiver).sub referenceContinuous).norm).div_const _
  have translationProfile (time : ℝ) (inside : time ∈ Icc 0 finish) :
      translation time ≤ constant * totalBudget / (changed.location (receiver.val + 1) ^ 4 * (nu - rate)) *
        Real.exp (nu * (time - finish)) := by
    have center := prepared.macroSourceState_center_difference time receiver
    rw [← prepared.referenceIdentity, norm_sub_rev] at center
    have normalized : translation time ≤ prepared.macroSourceState time receiver :=
      (div_le_iff₀ (changed.location_pos _)).mpr (by simpa only [mul_comm] using center)
    have selected := norm_le_pi_norm (fun current : Fin count => if current.val < drive.val then
      prepared.weightedMacroSourceState time current else 0) receiver
    have below : receiver.val < drive.val := by omega
    have receiverNonnegative : 0 ≤ prepared.weightedMacroSourceState time receiver :=
      mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time receiver)
    simp only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg receiverNonnegative] at selected
    have scaled := mul_le_mul_of_nonneg_left normalized (pow_nonneg receiverLocationPositive.le 4)
    have bound := scaled.trans (selected.trans (envelopeProfile time inside))
    have divided : translation time ≤ (constant * totalBudget / (nu - rate) *
        Real.exp (nu * (time - finish))) / changed.location (receiver.val + 1) ^ 4 :=
      (le_div_iff₀ (pow_pos receiverLocationPositive 4)).mpr (by simpa only [mul_comm] using bound)
    apply divided.trans_eq
    rw [div_mul_eq_mul_div, div_div, div_mul_eq_mul_div]
    congr 1
    ring
  have translationI := ((show Continuous (fun time : ℝ => Real.exp (-lambda * time)) by fun_prop).mul translationContinuous).intervalIntegrable (μ := volume) 0 finish
  have lambdaLess : lambda < nu := lambdaHalf.trans_lt (half_lt_self nuPositive)
  have secondGap : 0 < nu - lambda := sub_pos.mpr lambdaLess
  have comparison := intervalIntegral.exp_mul_integral_le_of_faster_exponential_majorant finishNonnegative lambdaLess
    (show 0 ≤ constant * totalBudget / (changed.location (receiver.val + 1) ^ 4 * (nu - rate)) by positivity)
    translationI translationProfile
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at comparison
  have exactBound : Real.exp (lambda * finish) * (∫ time in (0 : ℝ)..finish, Real.exp (-lambda * time) * translation time) ≤
      constant * totalBudget / (changed.location (receiver.val + 1) ^ 4 * (nu - rate) * (nu - lambda)) := by
    simpa only [div_div] using comparison
  have denominator : changed.location (receiver.val + 1) ^ 4 * nu ^ 2 / 4 ≤
      changed.location (receiver.val + 1) ^ 4 * (nu - rate) * (nu - lambda) := by
    have first : nu / 2 ≤ nu - rate := by
      simpa only [show nu - nu / 2 = nu / 2 by ring] using sub_le_sub_left rateHalf nu
    have second : nu / 2 ≤ nu - lambda := by
      simpa only [show nu - nu / 2 = nu / 2 by ring] using sub_le_sub_left lambdaHalf nu
    have product := mul_le_mul first second (half_pos nuPositive).le gapPositive.le
    convert mul_le_mul_of_nonneg_left product (pow_nonneg receiverLocationPositive.le 4) using 1 <;> ring
  have final := div_le_div_of_nonneg_left (mul_nonneg constantPositive.le totalNonnegative)
    (show 0 < changed.location (receiver.val + 1) ^ 4 * nu ^ 2 / 4 by positivity) denominator
  refine ⟨nuPositive, rateHalf, lambdaHalf, translationContinuous.continuousOn, translationI, exactBound, ?_⟩
  exact exactBound.trans (by (convert final using 1; ring))

end EulerNonuniqueness.Paper
