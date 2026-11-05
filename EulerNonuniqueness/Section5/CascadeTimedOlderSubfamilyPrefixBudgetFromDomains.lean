import EulerNonuniqueness.Section5.CascadeMixedFinerSubfamilyOriginalPrefixBudget
import EulerNonuniqueness.Section1.TimedOlderSharpSourcePrefixSeedBudget
import EulerNonuniqueness.Section6.SourcePacketBoundedRadiusNeutralSmall

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem exists_uniform_actual_timed_older_subfamily_prefix_budget_of_domains :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ coefficient : ℝ, 0 < coefficient →
    ∀ magnitudeMax distanceMax : ℝ, 0 ≤ magnitudeMax → 0 ≤ distanceMax →
    ∀ tailTolerance feedbackTolerance : ℝ, 0 < tailTolerance → 0 < feedbackTolerance →
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
    let older := Finset.univ.filter (fun source : Fin count => receiver.val + 1 < source.val)
    let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let forcing := prepared.selectedForeignForcing older receiver
    ContinuousOn forcing (Icc 0 path.stop) ∧
    ContinuousOn (fun time => prepared.macroSourceState time receiver) (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.macroSourceState time receiver) volume 0 finish ∧
    Real.exp (weight * entry nearest) *
      prepared.selectedMixedFinerSourcePrefixBudget older receiver incomingConstant outgoingConstant extent coefficient
        entry initialDistance magnitude weight finish ≤ tailTolerance * changed.seed (receiver.val + 1) / changed.ratio ^ 2 ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time) ≤
      tailTolerance * changed.seed (receiver.val + 1) / changed.ratio ^ 2 * Real.exp (-weight * entry nearest) +
      feedbackTolerance * (∫ time in (0 : ℝ)..finish,
        Real.exp (-weight * time) * prepared.macroSourceState time receiver) := by
  classical
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, integrationFactory⟩ :=
    exists_uniform_actual_mixed_finer_subfamily_original_prefix_budget
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, ?_⟩
  intro extent extentOne coefficient coefficientPositive magnitudeMax distanceMax magnitudeNonnegative distanceNonnegative
    tailTolerance feedbackTolerance tailPositive feedbackPositive scales amplitudePositive ratioBound alphaPositive alphaSmall
    ratioPower rateGap timingError timingErrorNonnegative ratioSeparation referenceConstant referenceNonnegative
    referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    factorPositive factorSmall rootOne boundaryOne
  have growthOne : (1 : ℝ) ≤ 2 * Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  filter_upwards [integrationFactory extent extentOne feedbackTolerance feedbackPositive scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
      factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_timed_older_sharp_source_prefix_seed_budget ratioBound alphaPositive alphaSmall ratioPower growthOne
      timingErrorNonnegative ratioSeparation sectionTime incomingNonnegative outgoingNonnegative (zero_le_one.trans extentOne)
      magnitudeNonnegative distanceNonnegative (show (0 : ℝ) ≤ 1 by norm_num) coefficientPositive tailPositive,
    scales.eventually_bounded_radius_source_neutral_small amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) (zero_lt_one.trans_le extentOne) (show (0 : ℝ) < 1 by norm_num),
    eventually_gt_atTop (0 : ℝ)] with frequency integration olderEstimate neutralEstimate frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance magnitude direction
    actualTime timeIdentity
  dsimp only
  intro nearestInside nearestTiming sourceTiming entries extents domains magnitudeBounds distanceBounds profiles finish finishInside
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let nearest : Fin count := ⟨receiver.val + 1, nonterminal⟩
  let older := Finset.univ.filter (fun source : Fin count => receiver.val + 1 < source.val)
  let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let neutral := fun source : Fin count => ‖centroidAsymmetry motion (entry source) source‖
  have olderBelow {source : Fin count} (member : source ∈ older) : receiver.val + 1 < source.val :=
    (Finset.mem_filter.mp member).2
  have ordered (source : Fin count) (member : source ∈ older) : receiver.val < source.val := by
    have := olderBelow member; omega
  have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
  have ratioPositive : 0 < changed.ratio := zero_lt_one.trans_le ratioOne
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (receiver.val + 1)
  have weightPositive : 0 < weight := mul_pos (zero_lt_one.trans_le growthOne) omegaPositive
  have rateBounds (source : Fin count) (member : source ∈ older) : 2 * weight ≤ coefficient * changed.omega (source.val + 1) := by
    have twoStep : changed.omega (receiver.val + 1) * changed.ratio ^ 2 ≤ changed.omega (source.val + 1) := by
      calc
        _ = changed.frequency * changed.ratio ^ (receiver.val + 1 + 2) := by simp only [Scales.omega, pow_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ratioOne (by have := olderBelow member; omega)) frequencyPositive.le
    have scaled := mul_le_mul_of_nonneg_right rateGap omegaPositive.le
    have last := mul_le_mul_of_nonneg_left twoStep coefficientPositive.le
    dsimp only [weight]
    nlinarith only [scaled, last]
  have data := integration count phase dipoleAngle prepared path receiver older ordered path.stop
    (nearestInside.1.trans nearestInside.2) le_rfl entry initialDistance direction
    (fun source member => by
      have actual := entries source (olderBelow member)
      exact ⟨actual.1, actual.2.1.trans nearestInside.2, actual.2.2⟩)
    (fun source member => extents source (olderBelow member)) coefficient coefficientPositive magnitude
    (fun source member => ⟨(magnitudeBounds source (olderBelow member)).1, profiles source (olderBelow member)⟩)
    finish finishInside weight weightPositive rateBounds
  dsimp only at data
  have neutralBounds (source : Fin count) (member : source ∈ older) : neutral source ≤ changed.length (source.val + 1) ^ 2 := by
    have sourceEntry := entries source (olderBelow member)
    have actual := neutralEstimate prepared.toCascadeMaterialPreparedPair path
      (thresholdBound.trans thresholdEighth |>.trans (by norm_num)) (factorSmall.trans (by norm_num)) source (entry source)
      sourceEntry.1 (sourceEntry.2.1.trans nearestInside.2) (domains source (olderBelow member)) (entry source) ⟨sourceEntry.1, le_rfl⟩
    simpa only [one_mul] using actual
  let paperIndex := fun source : Fin count => source.val + 1
  have paperInjective : Function.Injective paperIndex := fun first second equal => Fin.ext (Nat.add_right_cancel equal)
  let magnitudeNat := Function.extend paperIndex magnitude (fun _ => 0)
  let distanceNat := Function.extend paperIndex initialDistance (fun _ => 0)
  let neutralNat := Function.extend paperIndex neutral (fun _ => 0)
  have extendMagnitude (source : Fin count) : magnitudeNat (paperIndex source) = magnitude source := paperInjective.extend_apply _ _ _
  have extendDistance (source : Fin count) : distanceNat (paperIndex source) = initialDistance source := paperInjective.extend_apply _ _ _
  have extendNeutral (source : Fin count) : neutralNat (paperIndex source) = neutral source := paperInjective.extend_apply _ _ _
  have timeNearest : actualTime (receiver.val + 1 + 1) = entry nearest := by
    simpa only [nearest, Nat.add_assoc] using timeIdentity nearest
  have oldBound := olderEstimate count (receiver.val + 1) (older.image paperIndex)
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        exact ⟨by dsimp only [paperIndex]; have := olderBelow currentMember; omega, by dsimp only [paperIndex]; omega⟩)
    actualTime (by simpa only [Nat.add_assoc] using nearestTiming)
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        exact sourceTiming current (olderBelow currentMember))
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        rw [timeIdentity current, timeNearest]; exact (entries current (olderBelow currentMember)).2.1)
    magnitudeNat distanceNat neutralNat
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        rw [extendMagnitude]; exact magnitudeBounds current (olderBelow currentMember))
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        rw [extendDistance]; exact ⟨by linarith only [(entries current (olderBelow currentMember)).2.2.1], distanceBounds current (olderBelow currentMember)⟩)
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        rw [extendNeutral]; exact ⟨norm_nonneg _, by simpa only [one_mul] using neutralBounds current currentMember⟩)
  dsimp only at oldBound
  rw [Finset.sum_image (fun first _ second _ equal => paperInjective equal)] at oldBound
  let incomingTerm := fun source : Fin count => incomingConstant * extent ^ 2 *
    (changed.circulation (paperIndex source) * changed.length (paperIndex source) ^ 2 /
      |changed.location (receiver.val + 1) - changed.location (paperIndex source)| ^ 4 *
      (1 + changed.location (receiver.val + 1) / changed.location (paperIndex source))) * magnitude source /
      (coefficient * changed.omega (paperIndex source))
  let outgoingTerm := fun source : Fin count => outgoingConstant / changed.location (receiver.val + 1) ^ 4 * changed.circulation (paperIndex source) *
    (changed.circulation (paperIndex source) / weight ^ 2 +
      ((1 + initialDistance source) * changed.length (paperIndex source) ^ 2 + neutral source) / weight)
  let term := fun source : Fin count => (incomingTerm source + outgoingTerm source) * Real.exp (weight * (entry nearest - entry source))
  have sumBound : (∑ source ∈ older, term source) ≤ tailTolerance * changed.seed (receiver.val + 1) / changed.ratio ^ 2 := by
    simpa only [term, incomingTerm, outgoingTerm, extendMagnitude, extendDistance, extendNeutral, timeIdentity, timeNearest,
      paperIndex, weight, nearest, Nat.add_assoc] using oldBound
  have outgoingNonnegativeAt (source : Fin count) (member : source ∈ older) : 0 ≤ outgoingTerm source := by
    have distanceNonnegativeAt : 0 ≤ initialDistance source := by linarith only [(entries source (olderBelow member)).2.2.1]
    have circulationPositive := changed.circulation_pos frequencyPositive ratioPositive (paperIndex source)
    dsimp only [outgoingTerm, neutral]
    positivity
  have literalBound : Real.exp (weight * entry nearest) *
      prepared.selectedMixedFinerSourcePrefixBudget older receiver incomingConstant outgoingConstant extent coefficient
        entry initialDistance magnitude weight finish ≤ ∑ source ∈ older, term source := by
    have maskBound := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun source => entry source < finish) older)
      (fun source member _ => mul_nonneg (outgoingNonnegativeAt source member) (Real.exp_pos (-weight * entry source)).le)
    have expanded : prepared.selectedMixedFinerSourcePrefixBudget older receiver incomingConstant outgoingConstant extent coefficient
        entry initialDistance magnitude weight finish =
        (∑ source ∈ older, incomingTerm source * Real.exp (-weight * entry source)) +
        ∑ source ∈ older.filter (fun source => entry source < finish), outgoingTerm source * Real.exp (-weight * entry source) := by
      dsimp only [CascadeSourcePreparedPair.selectedMixedFinerSourcePrefixBudget, incomingTerm, outgoingTerm, paperIndex, neutral]
      simp_rw [Finset.mul_sum, mul_assoc]
      congr 1
      apply Finset.sum_congr rfl
      intro source _
      ring
    rw [expanded]
    apply (mul_le_mul_of_nonneg_left (add_le_add_left maskBound _) (Real.exp_pos _).le).trans_eq
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro source _
    have exponential : Real.exp (weight * entry nearest) * Real.exp (-weight * entry source) =
        Real.exp (weight * (entry nearest - entry source)) := by rw [← Real.exp_add]; congr 1; ring
    dsimp only [term]
    calc
      _ = (incomingTerm source + outgoingTerm source) *
          (Real.exp (weight * entry nearest) * Real.exp (-weight * entry source)) := by ring
      _ = _ := by rw [exponential]
  have normalized := literalBound.trans sumBound
  have cancellation : Real.exp (-weight * entry nearest) * Real.exp (weight * entry nearest) = 1 := by
    rw [← Real.exp_add]; simp only [neg_mul, neg_add_cancel, Real.exp_zero]
  have unscaled := mul_le_mul_of_nonneg_left normalized (Real.exp_pos (-weight * entry nearest)).le
  rw [← mul_assoc, cancellation, one_mul] at unscaled
  refine ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1, normalized, ?_⟩
  apply data.2.2.2.2.trans
  apply add_le_add_right
  simpa only [mul_comm] using unscaled

end EulerNonuniqueness.Paper
