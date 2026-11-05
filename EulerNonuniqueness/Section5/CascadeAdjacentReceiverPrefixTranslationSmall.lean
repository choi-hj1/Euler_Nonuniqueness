import EulerNonuniqueness.Section5.CascadeAdjacentReceiverPrefixTranslationBudget
import EulerNonuniqueness.Section1.TimedReceiverSourceAmplitudeSeedBudget
import EulerNonuniqueness.Section6.SourcePacketBoundedRadiusNeutralSmall
import EulerNonuniqueness.Section5.UniformSeedSmallness

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem exists_uniform_actual_adjacent_receiver_prefix_translation_small :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ coefficient : ℝ, 0 < coefficient → coefficient ≤ 1 →
    ∀ magnitudeMax distanceMax : ℝ, 0 ≤ magnitudeMax → 0 ≤ distanceMax →
    ∀ tolerance : ℝ, 0 < tolerance →
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max (max 2 (2 * responseConstant))
      (max (4 * responseConstant / coefficient) (4 * Real.sqrt 2 / coefficient)) ≤ scales.ratio →
    0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ timingError : ℝ, 0 ≤ timingError →
    (coefficient * scales.ratio + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude →
    ∀ threshold ≤ thresholdMax, ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant : ℝ),
    1 ≤ boundaryConstant → ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver drive : Fin count, receiver.val + 1 = drive.val → drive.val + 1 < count →
    ∀ entry initialDistance magnitude : Fin count → ℝ, ∀ direction : Fin count → ℂ, ∀ actualTime : ℕ → ℝ,
    (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
    0 ≤ entry drive → entry drive ≤ path.stop →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    |actualTime (drive.val + 1) - changed.predictedTime sectionTime count (drive.val + 1)| ≤
      timingError / changed.omega (drive.val + 1) →
    (∀ source : Fin count, drive.val < source.val →
      |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤
        timingError / changed.omega (source.val + 1)) →
    (∀ source : Fin count, drive.val < source.val →
      let length := changed.length (source.val + 1)
      0 ≤ entry source ∧ entry source ≤ entry drive ∧ 512 ≤ initialDistance source ∧
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
    (∀ source : Fin count, drive.val < source.val → ∀ time ∈ Icc 0 (entry source), ∀ patch,
      motion.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter motion time source)
        (extent * changed.length (source.val + 1))) →
    (∀ source : Fin count, drive.val < source.val → 0 ≤ magnitude source ∧ magnitude source ≤ magnitudeMax) →
    (∀ source : Fin count, drive.val < source.val → initialDistance source ≤ distanceMax) →
    let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    (∀ source : Fin count, drive.val < source.val → ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
      magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    (∀ time ∈ Icc 0 (entry drive), sharpState drive time ≤ magnitudeMax *
      Real.exp (coefficient * changed.omega (drive.val + 1) * (time - entry drive))) →
    (∀ current : Fin count, current.val < drive.val → ∀ time ∈ Icc 0 (entry drive),
      |unstableShape motion time current| + |stableShape motion time current| ≤ radius) →
    let lambda := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let translation := fun time => ‖quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver‖ /
      changed.location (receiver.val + 1)
    ContinuousOn translation (Icc 0 (entry drive)) ∧
    IntervalIntegrable (fun time => Real.exp (-lambda * time) * translation time) volume 0 (entry drive) ∧
    (changed.omega (receiver.val + 1) / changed.ratio) * Real.exp (lambda * entry drive) *
      (∫ time in (0 : ℝ)..entry drive, Real.exp (-lambda * time) * translation time) ≤ tolerance := by
  classical
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, incomingConstant, incomingNonnegative,
    outgoingConstant, outgoingNonnegative, factories⟩ := exists_uniform_actual_adjacent_receiver_prefix_translation_budget
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, factory⟩ :=
    factories factor factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro extent extentOne coefficient coefficientPositive coefficientOne magnitudeMax distanceMax magnitudeNonnegative
    distanceNonnegative tolerance tolerancePositive scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive
    alphaSmall ratioPower timingError timingErrorNonnegative ratioSeparation referenceConstant referenceNonnegative
    referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant boundaryOne
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ((le_max_left _ _).trans ratioLarge)
  have rootPositive : 0 < scaleRoot := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have halfPositive : 0 < tolerance / 2 := by positivity
  have driverDecay := (((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
    ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)).const_mul (constant * magnitudeMax / coefficient ^ 2)
  simp only [mul_zero, add_zero] at driverDecay
  filter_upwards [factory extent extentOne coefficient coefficientPositive scales scaleRoot rootLarge amplitudeIdentity
      ratioLarge alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime
      boundaryConstant boundaryOne,
    scales.eventually_timed_receiver_source_amplitude_seed_budget ratioBound alphaPositive alphaSmall ratioPower
      coefficientPositive coefficientOne timingErrorNonnegative ratioSeparation sectionTime incomingNonnegative outgoingNonnegative
      (zero_le_one.trans extentOne) magnitudeNonnegative distanceNonnegative (by norm_num : (0 : ℝ) ≤ 1)
      (show 0 ≤ 4 * constant by positivity) halfPositive,
    scales.eventually_bounded_radius_source_neutral_small amplitudePositive ratioBound alphaPositive rootPositive
      (zero_le_one.trans boundaryOne) (zero_lt_one.trans_le extentOne) (show (0 : ℝ) < 1 by norm_num),
    scales.eventually_seed_lt_one ratioBound alphaPositive,
    driverDecay.eventually (eventually_lt_nhds halfPositive), eventually_ge_atTop (1 : ℝ)]
    with frequency estimates oldEstimates neutralEstimate seedSmall driverSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver drive adjacent driveNonterminal
    entry initialDistance magnitude direction actualTime timeIdentity entryNonnegative entryBound
  dsimp only
  intro driveTiming sourceTiming entries extents domains magnitudeBounds distanceBounds profiles driverProfile small
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let receiverIndex := receiver.val + 1
  let nu := coefficient * changed.omega (drive.val + 1)
  let lambda := 2 * Real.sqrt 2 * changed.omega receiverIndex
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  let neutral := fun source : Fin count => ‖centroidAsymmetry motion (entry source) source‖
  let sourceBudget := ∑ source ∈ finer,
    (incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
      (1 + (changed.location (source.val + 1))⁻¹) * magnitude source +
      outgoingConstant * changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) / nu +
        (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 + neutral source)) *
      Real.exp (nu * (entry drive - entry source))
  let translation := fun time => ‖quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver‖ /
    changed.location receiverIndex
  have data := estimates count phase dipoleAngle prepared path receiver drive adjacent driveNonterminal (entry drive)
    entryNonnegative entryBound entry initialDistance direction entries extents magnitude magnitudeMax magnitudeNonnegative
    (fun source below => ⟨(magnitudeBounds source below).1, profiles source below⟩) driverProfile small
  dsimp only at data
  obtain ⟨_, _, _, translationContinuous, translationIntegrable, _, actionBound⟩ := data
  have neutralBounds (source : Fin count) (below : drive.val < source.val) : neutral source ≤ changed.length (source.val + 1) ^ 2 := by
    have sourceEntry := entries source below
    have actual := neutralEstimate prepared.toCascadeMaterialPreparedPair path (thresholdBound.trans thresholdEighth |>.trans (by norm_num))
      (factorSmall.trans (by norm_num)) source (entry source) sourceEntry.1 (sourceEntry.2.1.trans entryBound)
      (domains source below) (entry source) ⟨sourceEntry.1, le_rfl⟩
    simpa only [one_mul] using actual
  let paperIndex := fun source : Fin count => source.val + 1
  have paperInjective : Function.Injective paperIndex := fun first second equal => Fin.ext (Nat.add_right_cancel equal)
  let magnitudeNat := Function.extend paperIndex magnitude (fun _ => 0)
  let distanceNat := Function.extend paperIndex initialDistance (fun _ => 0)
  let neutralNat := Function.extend paperIndex neutral (fun _ => 0)
  have extendMagnitude (source : Fin count) : magnitudeNat (paperIndex source) = magnitude source := paperInjective.extend_apply _ _ _
  have extendDistance (source : Fin count) : distanceNat (paperIndex source) = initialDistance source := paperInjective.extend_apply _ _ _
  have extendNeutral (source : Fin count) : neutralNat (paperIndex source) = neutral source := paperInjective.extend_apply _ _ _
  have memberBelow {source : Fin count} (member : source ∈ finer) : drive.val < source.val := (Finset.mem_filter.mp member).2
  have driveIndex : drive.val + 1 = receiverIndex + 1 := by dsimp only [receiverIndex]; omega
  have timeDrive : actualTime (receiverIndex + 1) = entry drive := driveIndex ▸ timeIdentity drive
  have oldBound := oldEstimates count receiverIndex (finer.image paperIndex)
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        exact ⟨by dsimp only [paperIndex, receiverIndex]; have := memberBelow currentMember; omega, by dsimp only [paperIndex]; omega⟩)
    actualTime (by simpa only [← driveIndex] using driveTiming)
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        exact sourceTiming current (memberBelow currentMember))
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        rw [timeIdentity current, timeDrive]; exact (entries current (memberBelow currentMember)).2.1)
    magnitudeNat distanceNat neutralNat
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        rw [extendMagnitude]; exact magnitudeBounds current (memberBelow currentMember))
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        rw [extendDistance]; exact ⟨by linarith only [(entries current (memberBelow currentMember)).2.2.1], distanceBounds current (memberBelow currentMember)⟩)
    (by intro source member; obtain ⟨current, currentMember, rfl⟩ := Finset.mem_image.mp member
        rw [extendNeutral]; exact ⟨norm_nonneg _, by simpa only [one_mul] using neutralBounds current (memberBelow currentMember)⟩)
  dsimp only at oldBound
  rw [Finset.sum_image (fun first _ second _ equal => paperInjective equal)] at oldBound
  have oldAction : (changed.omega receiverIndex / changed.ratio) * (4 * constant) * sourceBudget /
      (changed.location receiverIndex ^ 4 * nu ^ 2) ≤ (tolerance / 2) * changed.seed receiverIndex / changed.ratio ^ 2 := by
    simpa only [sourceBudget, extendMagnitude, extendDistance, extendNeutral, timeIdentity, timeDrive, ← driveIndex,
      paperIndex, nu] using oldBound
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive receiverIndex
  have locationPositive := changed.location_pos receiverIndex
  have omegaOne : 1 ≤ changed.omega receiverIndex := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive
    (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]; positivity
  have seedFraction : changed.seed receiverIndex / changed.ratio ^ 2 ≤ 1 :=
    (div_le_one (pow_pos ratioPositive 2)).mpr ((seedSmall receiverIndex).le.trans (one_le_pow₀ ratioOne))
  have oldSmall : (changed.omega receiverIndex / changed.ratio) * (4 * constant) * sourceBudget /
      (changed.location receiverIndex ^ 4 * nu ^ 2) ≤ tolerance / 2 := oldAction.trans (by
    simpa only [mul_div_assoc, mul_one] using mul_le_mul_of_nonneg_left seedFraction halfPositive.le)
  have driverNumerator : 0 ≤ constant * rho * magnitudeMax / coefficient ^ 2 := by positivity
  have driverDenominator : 1 ≤ changed.ratio ^ 3 * changed.omega receiverIndex :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ ratioOne) omegaOne
  have driverBound : constant * rho * magnitudeMax / (coefficient ^ 2 * changed.ratio ^ 3 * changed.omega receiverIndex) ≤ tolerance / 2 := by
    have actual := (div_le_self driverNumerator driverDenominator).trans (by
      change constant * rho * magnitudeMax / coefficient ^ 2 ≤ tolerance / 2
      have bound : (constant * magnitudeMax / coefficient ^ 2) * rho < tolerance / 2 := by
        simpa only [mul_comm] using driverSmall
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using bound.le)
    convert actual using 1
    ring
  have omegaDrive : changed.omega (drive.val + 1) = changed.omega receiverIndex * changed.ratio := by
    rw [driveIndex]
    simp only [Scales.omega, pow_succ]; ring
  have locationDrive : changed.location (drive.val + 1) = changed.location receiverIndex / 2 := by
    rw [driveIndex]
    simp only [changed.location_eq_half_pow, pow_succ]; ring
  have nuIdentity : nu = coefficient * changed.ratio * changed.omega receiverIndex := by
    dsimp only [nu]; rw [omegaDrive]; ring
  have normalization : (changed.omega receiverIndex / changed.ratio) *
      (4 * constant * (4 * rho * changed.location (drive.val + 1) ^ 4 * magnitudeMax + sourceBudget) /
        (changed.location receiverIndex ^ 4 * nu ^ 2)) =
      constant * rho * magnitudeMax / (coefficient ^ 2 * changed.ratio ^ 3 * changed.omega receiverIndex) +
        (changed.omega receiverIndex / changed.ratio) * (4 * constant) * sourceBudget /
          (changed.location receiverIndex ^ 4 * nu ^ 2) := by
    rw [locationDrive, nuIdentity]
    field_simp [omegaPositive.ne', locationPositive.ne', coefficientPositive.ne', ratioPositive.ne']
    ring
  change Real.exp (lambda * entry drive) * (∫ time in (0 : ℝ)..entry drive, Real.exp (-lambda * time) * translation time) ≤
    4 * constant * (4 * rho * changed.location (drive.val + 1) ^ 4 * magnitudeMax + sourceBudget) /
      (changed.location receiverIndex ^ 4 * nu ^ 2) at actionBound
  refine ⟨translationContinuous, translationIntegrable, ?_⟩
  have scaled := mul_le_mul_of_nonneg_left actionBound (div_nonneg omegaPositive.le ratioPositive.le)
  rw [normalization] at scaled
  have final := scaled.trans (show
    constant * rho * magnitudeMax / (coefficient ^ 2 * changed.ratio ^ 3 * changed.omega receiverIndex) +
      (changed.omega receiverIndex / changed.ratio) * (4 * constant) * sourceBudget /
        (changed.location receiverIndex ^ 4 * nu ^ 2) ≤ tolerance by linarith only [driverBound, oldSmall])
  change (changed.omega receiverIndex / changed.ratio) * Real.exp (lambda * entry drive) *
    (∫ time in (0 : ℝ)..entry drive, Real.exp (-lambda * time) * translation time) ≤ tolerance
  simpa only [mul_assoc] using final

end EulerNonuniqueness.Paper
