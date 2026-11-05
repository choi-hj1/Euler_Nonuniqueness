import EulerNonuniqueness.Section5.CascadeTimedOlderSubfamilyPrefixBudgetFromDomains
import EulerNonuniqueness.Section5.CascadeMacroStateCenteredBound
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem older_input_le_six_nonnegative {first second third fourth fifth sixth : ℝ}
    (secondNonnegative : 0 ≤ second) (thirdNonnegative : 0 ≤ third) (fourthNonnegative : 0 ≤ fourth)
    (fifthNonnegative : 0 ≤ fifth) (sixthNonnegative : 0 ≤ sixth) :
    first ≤ first + second + third + fourth + fifth + sixth := by
  linarith only [secondNonnegative, thirdNonnegative, fourthNonnegative, fifthNonnegative, sixthNonnegative]

theorem exists_uniform_actual_timed_older_source_input_small :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ currentMagnitude : ℝ, 0 ≤ currentMagnitude → ∀ tolerance : ℝ, 0 < tolerance →
    ∀ extent : ℝ, 1 ≤ extent → ∀ coefficient : ℝ, 0 < coefficient →
    ∀ magnitudeMax distanceMax : ℝ, 0 ≤ magnitudeMax → 0 ≤ distanceMax →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 →
    4 < scales.ratio ^ scales.alpha → 4 * Real.sqrt 2 ≤ coefficient * scales.ratio ^ 2 →
    ∀ timingError : ℝ, 0 ≤ timingError →
    (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ (receiver : Fin count) (nonterminal : receiver.val + 1 < count),
    ∀ entry initialDistance magnitude : Fin count → ℝ, ∀ direction : Fin count → ℂ, ∀ actualTime : ℕ → ℝ,
    (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let nearest : Fin count := ⟨receiver.val + 1, nonterminal⟩
    entry nearest ∈ Icc 0 path.stop →
    |actualTime (receiver.val + 2) - changed.predictedTime sectionTime count (receiver.val + 2)| ≤
      timingError / changed.omega (receiver.val + 2) →
    (∀ source : Fin count, receiver.val + 1 < source.val →
      |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤
        timingError / changed.omega (source.val + 1)) →
    (∀ source : Fin count, receiver.val + 1 < source.val →
      let length := changed.length (source.val + 1)
      0 ≤ entry source ∧ entry source ≤ entry nearest ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entry source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion (entry source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
          secondDipoleCenter motion (entry source) source)).re ∧
      ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
        (5 / 4 : ℝ) * length * initialDistance source) →
    (∀ source : Fin count, receiver.val + 1 < source.val → ∀ time ∈ Icc 0 (entry source),
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
        extent * changed.length (source.val + 1))) →
    (∀ source : Fin count, receiver.val + 1 < source.val → ∀ time ∈ Icc 0 (entry source), ∀ patch,
      motion.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter motion time source)
        (extent * changed.length (source.val + 1))) →
    (∀ source : Fin count, receiver.val + 1 < source.val → 0 ≤ magnitude source ∧ magnitude source ≤ magnitudeMax) →
    (∀ source : Fin count, receiver.val + 1 < source.val → initialDistance source ≤ distanceMax) →
    let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    (∀ source : Fin count, receiver.val + 1 < source.val → ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
      magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    ∀ finish ∈ Icc 0 path.stop,
    (∀ time ∈ Icc 0 finish, sharpState receiver time ≤ currentMagnitude * changed.seed (receiver.val + 1) *
      Real.exp ((2 * Real.sqrt 2 * changed.omega (receiver.val + 1)) * (time - entry nearest))) →
    let older := Finset.univ.filter (fun source : Fin count => receiver.val + 1 < source.val)
    let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let forcing := prepared.selectedForeignForcing older receiver
    let leading := fun time => ∑ source ∈ older, relativeBlockSourceShapeInput changed motion prepared.reference receiver source time
    ContinuousOn forcing (Icc 0 path.stop) ∧
    ContinuousOn (fun time => prepared.macroSourceState time receiver) (Icc 0 path.stop) ∧
    ContinuousOn leading (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.macroSourceState time receiver) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) • leading time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖leading time‖) volume 0 finish ∧
    Real.exp (weight * entry nearest) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time) ≤ tolerance * changed.seed (receiver.val + 1) ∧
    Real.exp (weight * entry nearest) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖leading time‖) ≤ tolerance * changed.seed (receiver.val + 1) := by
  classical
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, factories⟩ :=
    exists_uniform_actual_timed_older_subfamily_prefix_budget_of_domains
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro currentMagnitude currentNonnegative tolerance tolerancePositive extent extentOne coefficient coefficientPositive
    magnitudeMax distanceMax magnitudeNonnegative distanceNonnegative scales amplitudePositive ratioBound alphaPositive alphaSmall
    ratioPower rateGap timingError timingErrorNonnegative ratioSeparation referenceConstant referenceNonnegative
    referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    factorPositive factorSmall rootOne boundaryOne
  let feedbackTolerance := tolerance / (8 * (1 + currentMagnitude))
  have feedbackPositive : 0 < feedbackTolerance := by dsimp only [feedbackTolerance]; positivity
  have halfPositive : 0 < tolerance / 2 := by positivity
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [factories extent extentOne coefficient coefficientPositive magnitudeMax distanceMax magnitudeNonnegative
      distanceNonnegative (tolerance / 2) feedbackTolerance halfPositive feedbackPositive scales amplitudePositive ratioBound
      alphaPositive alphaSmall ratioPower rateGap timingError timingErrorNonnegative ratioSeparation referenceConstant
      referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
      factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_length_lt_location ratioBound alphaPositive (show (0 : ℝ) < 1 by norm_num),
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans thresholdEighth) referenceNonnegative rootOne boundaryOne factorPositive factorOne]
    with frequency estimates lengths inputs
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance magnitude direction
    actualTime timeIdentity
  dsimp only
  intro nearestInside nearestTiming sourceTiming entries extents domains magnitudeBounds distanceBounds profiles finish finishInside currentProfile
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let nearest : Fin count := ⟨receiver.val + 1, nonterminal⟩
  let older := Finset.univ.filter (fun source : Fin count => receiver.val + 1 < source.val)
  let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let forcing := prepared.selectedForeignForcing older receiver
  let leading := fun time => ∑ source ∈ older, relativeBlockSourceShapeInput changed motion prepared.reference receiver source time
  have data := estimates count phase dipoleAngle prepared path receiver nonterminal entry initialDistance magnitude direction
    actualTime timeIdentity nearestInside nearestTiming sourceTiming entries extents domains magnitudeBounds distanceBounds profiles finish finishInside
  dsimp only at data
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishInside.2
  have leadingContinuous : ContinuousOn leading (Icc 0 path.stop) := by
    apply continuousOn_finset_sum
    intro source member
    have below := (Finset.mem_filter.mp member).2
    have different : receiver ≠ source := by intro equal; subst source; omega
    exact inputs count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source different
  have exponentialContinuous : ContinuousOn (fun time : ℝ => Real.exp (-weight * time)) (Icc 0 finish) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have leadingIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) • leading time) volume 0 finish :=
    (exponentialContinuous.smul (leadingContinuous.mono subset)).intervalIntegrable_of_Icc finishInside.1
  have leadingNormIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖leading time‖) volume 0 finish :=
    (exponentialContinuous.mul (leadingContinuous.norm.mono subset)).intervalIntegrable_of_Icc finishInside.1
  have macroBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.macroSourceState time receiver ≤
        4 * currentMagnitude * changed.seed (receiver.val + 1) * Real.exp (weight * (time - entry nearest)) := by
    have actual := prepared.macroSourceState_le_centered_and_raw path (subset inside) receiver
    rw [← prepared.referenceIdentity, norm_sub_rev] at actual
    have lengthRatio : changed.length (receiver.val + 1) / changed.location (receiver.val + 1) ≤ 1 :=
      (div_le_one (changed.location_pos _)).mpr (by simpa only [one_mul] using (lengths (receiver.val + 1)).le)
    have centeredNonnegative : 0 ≤ prepared.rawSourceCenteredState time receiver :=
      div_nonneg (norm_nonneg _) (changed.length_pos _).le
    have rawNonnegative : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch := by
      apply Finset.sum_nonneg; intro patch _; dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
    have centerNonnegative := div_nonneg (norm_nonneg (quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver))
      (changed.location_pos (receiver.val + 1)).le
    have momentNonnegative := norm_nonneg (relativeNormalizedFirstMoment changed motion prepared.reference receiver time)
    have centeredScaled := mul_le_mul_of_nonneg_right lengthRatio
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) centeredNonnegative)
    have sharp := currentProfile time inside
    change _ ≤ currentMagnitude * changed.seed (receiver.val + 1) * Real.exp (weight * (time - entry nearest)) at sharp
    nlinarith only [actual, centeredScaled, sharp, rawNonnegative, centerNonnegative, momentNonnegative]
  have weightedMacroBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      Real.exp (-weight * time) * prepared.macroSourceState time receiver ≤
        4 * currentMagnitude * changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest) := by
    have actual := mul_le_mul_of_nonneg_left (macroBound time inside) (Real.exp_pos (-weight * time)).le
    have exponential : Real.exp (-weight * time) * Real.exp (weight * (time - entry nearest)) =
        Real.exp (-weight * entry nearest) := by rw [← Real.exp_add]; congr 1; ring
    apply actual.trans_eq
    calc
      _ = (4 * currentMagnitude * changed.seed (receiver.val + 1)) *
          (Real.exp (-weight * time) * Real.exp (weight * (time - entry nearest))) := by ring
      _ = _ := by rw [exponential]
  have seedNonnegative : 0 ≤ changed.seed (receiver.val + 1) := by dsimp only [Scales.seed]; positivity
  have macroAction :
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.macroSourceState time receiver) ≤
        4 * currentMagnitude * changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest) := by
    have constantIntegrable : IntervalIntegrable
        (fun _ : ℝ => 4 * currentMagnitude * changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest)) volume 0 finish :=
      intervalIntegrable_const
    have integrated := intervalIntegral.integral_mono_on finishInside.1 data.2.2.2.1 constantIntegrable weightedMacroBound
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at integrated
    have finishOne : finish ≤ 1 := finishInside.2.trans path.stopBound
    exact integrated.trans (mul_le_of_le_one_left (by positivity) finishOne)
  have feedbackCoefficient : feedbackTolerance * (4 * currentMagnitude) ≤ tolerance / 2 := by
    have ratio := (div_le_one (by positivity : 0 < 1 + currentMagnitude)).mpr
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
    have identity : feedbackTolerance * (4 * currentMagnitude) = (tolerance / 2) * (currentMagnitude / (1 + currentMagnitude)) := by
      dsimp only [feedbackTolerance]
      field_simp
      ring
    rw [identity]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ratio halfPositive.le
  have feedbackAction : feedbackTolerance *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.macroSourceState time receiver) ≤
        (tolerance / 2) * changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest) := by
    calc
      _ ≤ feedbackTolerance * (4 * currentMagnitude * changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest)) :=
        mul_le_mul_of_nonneg_left macroAction feedbackPositive.le
      _ = (feedbackTolerance * (4 * currentMagnitude)) * (changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest)) := by ring
      _ ≤ _ := by
        simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right feedbackCoefficient
          (mul_nonneg seedNonnegative (Real.exp_pos _).le))
  have ratioSquareOne : 1 ≤ changed.ratio ^ 2 := one_le_pow₀ (by change 1 ≤ scales.ratio; linarith only [ratioBound])
  have tailBound : (tolerance / 2) * changed.seed (receiver.val + 1) / changed.ratio ^ 2 *
      Real.exp (-weight * entry nearest) ≤
        (tolerance / 2) * changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest) :=
    mul_le_mul_of_nonneg_right (div_le_self (mul_nonneg halfPositive.le seedNonnegative) ratioSquareOne) (Real.exp_pos _).le
  have forcingAction :
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time) ≤
        tolerance * changed.seed (receiver.val + 1) * Real.exp (-weight * entry nearest) := by
    have bound := data.2.2.2.2.2.trans (add_le_add tailBound feedbackAction)
    convert bound using 1; ring
  have forcingNormalized : Real.exp (weight * entry nearest) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time) ≤
        tolerance * changed.seed (receiver.val + 1) := by
    have cancellation : Real.exp (weight * entry nearest) * Real.exp (-weight * entry nearest) = 1 := by
      rw [← Real.exp_add]; simp only [neg_mul, add_neg_cancel, Real.exp_zero]
    have actual := mul_le_mul_of_nonneg_left forcingAction (Real.exp_pos (weight * entry nearest)).le
    apply actual.trans_eq
    calc
      _ = (tolerance * changed.seed (receiver.val + 1)) *
          (Real.exp (weight * entry nearest) * Real.exp (-weight * entry nearest)) := by ring
      _ = _ := by rw [cancellation, mul_one]
  have leadingBound (time : ℝ) : ‖leading time‖ ≤ forcing time := by
    have locationPositive := changed.location_pos (receiver.val + 1)
    have lengthPositive := changed.length_pos (receiver.val + 1)
    dsimp only [forcing, leading, CascadeSourcePreparedPair.selectedForeignForcing]
    apply older_input_le_six_nonnegative <;>
      dsimp only [CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm] <;>
      positivity
  have leadingAction := intervalIntegral.integral_mono_on finishInside.1 leadingNormIntegrable data.2.2.1
    (fun time _ => mul_le_mul_of_nonneg_left (leadingBound time) (Real.exp_pos (-weight * time)).le)
  refine ⟨data.1, data.2.1, leadingContinuous, data.2.2.1, data.2.2.2.1, leadingIntegrable, leadingNormIntegrable,
    forcingNormalized, ?_⟩
  exact (mul_le_mul_of_nonneg_left leadingAction (Real.exp_pos (weight * entry nearest)).le).trans forcingNormalized

end EulerNonuniqueness.Paper

