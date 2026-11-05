import EulerNonuniqueness.Section5.CascadeQuantitativeFirstSeparation
import EulerNonuniqueness.Section5.CascadeAccurateOutgoingData

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_uniform_actual_first_separation_outgoing_data
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (incomingTime modelSection : ℝ) (modelDerivative : ℝ → ℝ)
    (sectionAfter : incomingTime + 1 < modelSection) (radiusLarge : 512 ≤ separationRadius orbit modelSection)
    (transverse : ∀ time ∈ Icc (modelSection - 1) (modelSection + 1),
      HasDerivAt (separationRadius orbit) (modelDerivative time) time ∧ 1 ≤ modelDerivative time)
    (earlierMargin : ∀ time ≤ modelSection - 1,
      separationRadius orbit time ≤ separationRadius orbit modelSection - 1)
    {factor accuracy error : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
    (accuracyPositive : 0 < accuracy) (errorPositive : 0 < error) (errorSmall : error ≤ 1 / 64)
    (referenceSeparated : ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖)
    (separationClose : ‖orbit.positive modelSection + orbit.negative modelSection -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ error / 2)
    (referenceOutgoing : (7 / 8 : ℝ) * separationRadius orbit modelSection ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive modelSection - orbit.negative modelSection)).re) :
    ∃ tolerance > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ sectionTime : ℝ, ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 0 < scaleRoot → 0 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ hit ∈ Icc 0 path.stop,
    (∀ current ∈ Icc 0 hit, |radialShape prepared.trajectory.movingFamily.patchMotion current index| ≤ 1 / 2) →
    ∀ rotation : ℂ, ‖rotation‖ = 1 →
    ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
      index hit rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ tolerance →
    let changed : Scales := {scales with frequency := frequency}
    let omega := changed.omega (index.val + 1)
    let length := changed.length (index.val + 1)
    let radius := separationRadius orbit modelSection
    let direction := rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
    let endpoint := hit + (modelSection + 1 - incomingTime) / omega
    endpoint ≤ 1 →
    (∀ other : Fin count, other ≠ index → ∀ current ∈ Icc hit (min path.stop endpoint),
      ∀ first second : Fin 4, first ≠ second →
        factor * changed.length (other.val + 1) <
          ‖patchCentroid prepared.trajectory.movingFamily.patchMotion current other first -
            patchCentroid prepared.trajectory.movingFamily.patchMotion current other second‖) →
    endpoint ≤ path.stop ∧
    ∃ contact ∈ Icc (hit + (modelSection - incomingTime - 1) / omega) endpoint,
      FirstSeparationTime changed orbit modelSection prepared.trajectory.movingFamily.patchMotion index contact ∧
      (∀ earlier ∈ Ico 0 contact, pairCenterDistance prepared.trajectory.movingFamily.patchMotion earlier index <
        radius * length) ∧
      |contact - (hit + (modelSection - incomingTime) / omega)| ≤ 2 * accuracy / omega ∧
      ‖firstDipoleCenter prepared.trajectory.movingFamily.patchMotion contact index -
        secondDipoleCenter prepared.trajectory.movingFamily.patchMotion contact index‖ = length * radius ∧
      ‖firstDipoleSeparation prepared.trajectory.movingFamily.patchMotion contact index - (length : ℂ) * direction‖ ≤
        error * length ∧
      ‖secondDipoleSeparation prepared.trajectory.movingFamily.patchMotion contact index - (length : ℂ) * (-direction)‖ ≤
        error * length ∧
      (3 / 4 : ℝ) * length * radius ≤
        (Complex.I * star direction * (firstDipoleCenter prepared.trajectory.movingFamily.patchMotion contact index -
          secondDipoleCenter prepared.trajectory.movingFamily.patchMotion contact index)).re ∧
      ‖firstDipoleCenter prepared.trajectory.movingFamily.patchMotion contact index -
        secondDipoleCenter prepared.trajectory.movingFamily.patchMotion contact index‖ ≤ (5 / 4 : ℝ) * length * radius := by
  let profile := fun time => centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time)
  have positiveContinuous := (normalized.2.1 modelSection).2.2.1.continuousAt
  have negativeContinuous := (normalized.2.1 modelSection).2.2.2.continuousAt
  have profileContinuous : ContinuousAt profile modelSection := by
    apply continuousAt_pi.mpr
    intro patch
    fin_cases patch
    · simpa only [profile, centrallySymmetricFourPoint] using positiveContinuous
    · simpa only [profile, centrallySymmetricFourPoint] using positiveContinuous.neg
    · simpa only [profile, centrallySymmetricFourPoint] using negativeContinuous
    · simpa only [profile, centrallySymmetricFourPoint] using negativeContinuous.neg
  obtain ⟨delta, deltaPositive, closeProfile⟩ := Metric.continuousAt_iff.mp profileContinuous (error / 8) (by positivity)
  let comparisonAccuracy := min accuracy (min (error / 8) (min (delta / 4) (1 / 4)))
  have comparisonPositive : 0 < comparisonAccuracy := lt_min accuracyPositive
    (lt_min (by positivity) (lt_min (by positivity) (by norm_num)))
  have comparisonTiming : comparisonAccuracy ≤ accuracy := min_le_left _ _
  have comparisonError : comparisonAccuracy ≤ error / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have comparisonDelta : comparisonAccuracy ≤ delta / 4 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have comparisonHalf : comparisonAccuracy < 1 / 2 := by
    have quarter : comparisonAccuracy ≤ 1 / 4 :=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
    linarith only [quarter]
  obtain ⟨firstTolerance, firstPositive, firstFactory⟩ := exists_uniform_actual_quantitative_first_separation orbit normalized
    incomingTime modelSection modelDerivative sectionAfter radiusLarge transverse earlierMargin factorPositive factorSmall
    comparisonPositive comparisonHalf referenceSeparated
  let horizon := modelSection + 1 - incomingTime
  have horizonPositive : 0 < horizon := by dsimp only [horizon]; linarith only [sectionAfter]
  obtain ⟨shadowTolerance, shadowPositive, shadowFactory⟩ := exists_universal_material_paper_label_passage_shadowing
    orbit normalized incomingTime horizon horizonPositive comparisonAccuracy comparisonPositive factorPositive
      (factorSmall.trans (by norm_num))
  refine ⟨min firstTolerance shadowTolerance, lt_min firstPositive shadowPositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootPositive boundaryNonnegative
  filter_upwards [firstFactory scales amplitudePositive ratioBound alphaPositive sectionTime thresholdSmall
      referenceNonnegative rootPositive boundaryNonnegative,
    shadowFactory scales amplitudePositive ratioBound alphaPositive sectionTime rootPositive boundaryNonnegative,
    eventually_gt_atTop (0 : ℝ)] with frequency firstEstimate shadowEstimate frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal hit hitInside radialSmall rotation rotationNorm initial
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let length := changed.length (index.val + 1)
  let endpoint := hit + horizon / omega
  intro endpointOne otherGaps
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  obtain ⟨endpointAvailable, contact, contactInside, firstContact, earlierStrict, timingSmall⟩ :=
    firstEstimate count phase dipoleAngle prepared path index nonterminal hit hitInside radialSmall rotation rotationNorm
      (initial.trans (min_le_left _ _)) endpointOne otherGaps
  let fastTime := omega * (contact - hit)
  have physical : hit + fastTime / omega = contact := by dsimp only [fastTime]; field_simp
  have hitBeforeContact : hit ≤ contact := by
    have offset : 0 ≤ (modelSection - incomingTime - 1) / omega := div_nonneg
      (by linarith only [sectionAfter]) omegaPositive.le
    exact (le_add_of_nonneg_right offset).trans contactInside.1
  have fastInside : fastTime ∈ Icc 0 horizon := by
    refine ⟨mul_nonneg omegaPositive.le (sub_nonneg.mpr hitBeforeContact), ?_⟩
    have difference : contact - hit ≤ horizon / omega := by linarith only [contactInside.2]
    have scaled := (le_div_iff₀ omegaPositive).mp difference
    dsimp only [fastTime]
    nlinarith only [scaled]
  have fastTiming : |fastTime + incomingTime - modelSection| ≤ 2 * comparisonAccuracy := by
    have identity : fastTime + incomingTime - modelSection =
        omega * (contact - (hit + (modelSection - incomingTime) / omega)) := by
      dsimp only [fastTime]
      field_simp [omegaPositive.ne']
      ring
    rw [identity, abs_mul, abs_of_pos omegaPositive]
    have scaled := mul_le_mul_of_nonneg_left timingSmall omegaPositive.le
    have cancellation : omega * (2 * comparisonAccuracy / omega) = 2 * comparisonAccuracy := by
      field_simp [omegaPositive.ne']
    exact scaled.trans_eq cancellation
  have closeReference : ‖profile (fastTime + incomingTime) - profile modelSection‖ < error / 8 := by
    have distance : dist (fastTime + incomingTime) modelSection < delta := by
      rw [Real.dist_eq]
      exact fastTiming.trans_lt (by linarith only [comparisonDelta, deltaPositive])
    simpa only [dist_eq_norm] using closeProfile distance
  have inside (time : ℝ) (member : time ∈ Icc 0 horizon) : hit + time / omega ∈ Icc 0 path.stop :=
    ⟨add_nonneg hitInside.1 (div_nonneg member.1 omegaPositive.le),
      (add_le_add_left (div_le_div_of_nonneg_right member.2 omegaPositive.le) hit).trans endpointAvailable⟩
  have shadow := shadowEstimate count phase dipoleAngle prepared path index hit horizon horizonPositive le_rfl rotation rotationNorm
    inside (initial.trans (min_le_right _ _)) fastTime fastInside
  have fixedClose : ‖cascadeNormalizedPointPositions changed motion index hit rotation fastTime -
      profile modelSection‖ ≤ error / 4 := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (cascadeNormalizedPointPositions changed motion index hit rotation fastTime) (profile (fastTime + incomingTime))
      (profile modelSection)
    nlinarith only [triangle, shadow, closeReference, comparisonError]
  have outgoing := cascadeNormalizedPointPositions_outgoing_data_with_error changed motion index hit fastTime
    (positive := orbit.positive modelSection) (negative := orbit.negative modelSection)
    (direction := Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) errorPositive.le errorSmall
    rotationNorm (by simp [Complex.norm_exp, Complex.mul_re]) radiusLarge separationClose referenceOutgoing fixedClose
  dsimp only at outgoing
  have physicalLiteral : hit + fastTime / changed.omega (index.val + 1) = contact := physical
  simp only [physicalLiteral] at outgoing
  refine ⟨endpointAvailable, contact, contactInside, firstContact, earlierStrict, ?_, ?_, outgoing⟩
  · exact timingSmall.trans (div_le_div_of_nonneg_right (by linarith only [comparisonTiming]) omegaPositive.le)
  · have equality := firstContact.2.1
    change ‖firstDipoleCenter motion contact index - secondDipoleCenter motion contact index‖ =
      separationRadius orbit modelSection * length at equality
    exact equality.trans (mul_comm _ _)

end EulerNonuniqueness.Paper

