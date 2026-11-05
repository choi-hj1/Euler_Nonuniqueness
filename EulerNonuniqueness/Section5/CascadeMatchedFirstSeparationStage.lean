import EulerNonuniqueness.Section5.CascadeFirstSeparationOutgoingData
import EulerNonuniqueness.Section5.CascadeUniformMatchedPassageDomainExtent
import EulerNonuniqueness.Section5.UniversalMatchedPassageContinuation
import EulerNonuniqueness.Section5.CascadeTerminalSectionContinuation

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_uniform_actual_matched_first_separation_stage
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (modelSection : ℝ) (modelDerivative : ℝ → ℝ)
    (radiusLarge : 512 ≤ separationRadius orbit modelSection)
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
    ∃ extent ≥ (4 : ℝ), ∀ incomingTime : ℝ, incomingTime + 1 < modelSection →
    ∃ tolerance > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 0 < scaleRoot → 0 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit modelSection phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ hit ∈ Icc 0 path.stop,
    (∀ current ∈ Icc 0 hit, |radialShape prepared.trajectory.movingFamily.patchMotion current index| ≤ 1 / 2) →
    ∀ rotation : ℂ, ‖rotation‖ = 1 →
    ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
      index hit rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ tolerance →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let omega := changed.omega (index.val + 1)
    let length := changed.length (index.val + 1)
    let radius := separationRadius orbit modelSection
    let direction := rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
    let endpoint := hit + (modelSection + 1 - incomingTime) / omega
    endpoint ≤ 1 →
    (∀ other : Fin count, other ≠ index → other.val + 1 < count →
      (∀ current ∈ Icc 0 (min path.stop endpoint), |radialShape motion current other| ≤ 1 / 2) ∨
      ∃ start ∈ Icc 0 hit, ∃ otherRotation : ℂ, ‖otherRotation‖ = 1 ∧
        ‖cascadeNormalizedPointPositions changed motion other start otherRotation 0 -
          centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ tolerance) →
    endpoint ≤ path.stop ∧ ‖direction‖ = 1 ∧
    ∃ contact ∈ Icc (hit + (modelSection - incomingTime - 1) / omega) endpoint,
      FirstSeparationTime changed orbit modelSection motion index contact ∧
      (∀ earlier ∈ Ico 0 contact, pairCenterDistance motion earlier index < radius * length) ∧
      |contact - (hit + (modelSection - incomingTime) / omega)| ≤ 2 * accuracy / omega ∧
      ‖firstDipoleCenter motion contact index - secondDipoleCenter motion contact index‖ = length * radius ∧
      ‖firstDipoleSeparation motion contact index - (length : ℂ) * direction‖ ≤ error * length ∧
      ‖secondDipoleSeparation motion contact index - (length : ℂ) * (-direction)‖ ≤ error * length ∧
      (3 / 4 : ℝ) * length * radius ≤
        (Complex.I * star direction * (firstDipoleCenter motion contact index - secondDipoleCenter motion contact index)).re ∧
      ‖firstDipoleCenter motion contact index - secondDipoleCenter motion contact index‖ ≤ (5 / 4 : ℝ) * length * radius ∧
      ∀ time ∈ Icc 0 contact, ∀ patch : Fin 4,
        ‖patchCentroid motion time index patch - quadrupoleCenter motion time index‖ ≤ extent * length ∧
        ‖patchCentroid reference time index patch - quadrupoleCenter reference time index‖ ≤ extent * length ∧
        motion.domain time index patch ⊆ closedBall (quadrupoleCenter motion time index) (extent * length) ∧
        reference.domain time index patch ⊆ closedBall (quadrupoleCenter reference time index) (extent * length) := by
  obtain ⟨extent, extentFour, domains⟩ := exists_uniform_actual_matched_passage_domain_extent_all_incoming
    orbit normalized (modelSection + 1)
  refine ⟨extent, extentFour, ?_⟩
  intro incomingTime sectionAfter
  have timeOrder : incomingTime < modelSection := by linarith only [sectionAfter]
  have domainOrder : incomingTime < modelSection + 1 := by linarith only [sectionAfter]
  obtain ⟨firstTolerance, firstPositive, firstFactory⟩ := exists_uniform_actual_first_separation_outgoing_data
    orbit normalized incomingTime modelSection modelDerivative sectionAfter radiusLarge transverse earlierMargin
    factorPositive factorSmall accuracyPositive errorPositive errorSmall referenceSeparated separationClose referenceOutgoing
  obtain ⟨domainTolerance, domainPositive, domainFactory⟩ := domains incomingTime domainOrder factor factorPositive factorSmall
  obtain ⟨matchedTolerance, matchedPositive, matchedFactory⟩ := exists_universal_material_matched_passage_continuation
    orbit normalized incomingTime modelSection timeOrder factorPositive factorSmall errorPositive errorSmall
    referenceSeparated radiusLarge separationClose referenceOutgoing
  let tolerance := min firstTolerance (min domainTolerance matchedTolerance)
  have tolerancePositive : 0 < tolerance := lt_min firstPositive (lt_min domainPositive matchedPositive)
  have firstToleranceBound : tolerance ≤ firstTolerance := min_le_left _ _
  have domainToleranceBound : tolerance ≤ domainTolerance := (min_le_right _ _).trans (min_le_left _ _)
  have matchedToleranceBound : tolerance ≤ matchedTolerance := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨tolerance, tolerancePositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootPositive boundaryNonnegative
  have separationCoarse : ‖orbit.positive modelSection + orbit.negative modelSection -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ 1 / 128 := by
    linarith only [separationClose, errorSmall]
  filter_upwards [firstFactory scales amplitudePositive ratioBound alphaPositive modelSection thresholdSmall referenceNonnegative
      rootPositive boundaryNonnegative,
    domainFactory scales amplitudePositive ratioBound alphaPositive modelSection thresholdSmall referenceNonnegative
      rootPositive boundaryNonnegative,
    matchedFactory scales amplitudePositive ratioBound alphaPositive modelSection rootPositive boundaryNonnegative,
    scales.eventually_material_prehit_internal_gap amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    cascade_terminal_gap_continuation_of_section orbit modelSection radiusLarge separationCoarse referenceOutgoing
      scales amplitudePositive ratioBound alphaPositive factorPositive factorSmall rootPositive boundaryNonnegative,
    eventually_gt_atTop (0 : ℝ)] with frequency firstEstimate domainEstimate matched prehit terminal frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal hit hitInside radialSmall rotation rotationNorm initial
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let endpoint := hit + (modelSection + 1 - incomingTime) / omega
  intro endpointOne stages
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have endpointNonnegative : 0 ≤ endpoint := add_nonneg hitInside.1
    (div_nonneg (by linarith only [sectionAfter]) omegaPositive.le)
  have windowNonnegative : 0 ≤ min path.stop endpoint := le_min path.stopPositive.le endpointNonnegative
  have otherGaps (other : Fin count) (different : other ≠ index)
      (current : ℝ) (inside : current ∈ Icc hit (min path.stop endpoint))
      (first second : Fin 4) (patchDifferent : first ≠ second) :
      factor * changed.length (other.val + 1) <
        ‖patchCentroid motion current other first - patchCentroid motion current other second‖ := by
    by_cases last : other.val + 1 = count
    · have gap := terminal count phase dipoleAngle prepared path other last current
        ⟨hitInside.1.trans inside.1, inside.2.trans (min_le_left _ _)⟩ first second patchDifferent
      have positive := changed.length_pos (other.val + 1)
      have strict : factor * changed.length (other.val + 1) < changed.length (other.val + 1) / 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right factorSmall positive.le, positive]
      exact strict.trans_le gap
    have otherNonterminal : other.val + 1 < count := by omega
    rcases stages other different otherNonterminal with radial | ⟨start, startInside, otherRotation, otherNorm, initialOther⟩
    · exact (prehit prepared path (thresholdSmall.trans (by norm_num)) factorSmall other otherNonterminal
        (min path.stop endpoint) windowNonnegative (min_le_left _ _) radial current
        ⟨hitInside.1.trans inside.1, inside.2⟩).1 first second patchDifferent
    · exact matched count phase dipoleAngle prepared path other start startInside.1 (startInside.2.trans hitInside.2)
        otherRotation otherNorm (initialOther.trans matchedToleranceBound) current
        ⟨startInside.2.trans inside.1, inside.2.trans (min_le_left _ _)⟩ first second patchDifferent
  obtain ⟨endpointAvailable, contact, contactInside, firstContact, earlierStrict, timing, pairNorm,
    firstEntry, secondEntry, projection, upper⟩ :=
    firstEstimate count phase dipoleAngle prepared path index nonterminal hit hitInside radialSmall rotation rotationNorm
      (initial.trans firstToleranceBound) endpointOne otherGaps
  have directionNorm : ‖rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ = 1 := by
    simp [norm_mul, rotationNorm, Complex.norm_exp, Complex.mul_re]
  refine ⟨endpointAvailable, directionNorm, contact, contactInside, firstContact, earlierStrict, timing, pairNorm,
    firstEntry, secondEntry, projection, upper, ?_⟩
  intro time inside patch
  have available : time ∈ Icc 0 (min path.stop endpoint) :=
    ⟨inside.1, le_min (inside.2.trans (contactInside.2.trans endpointAvailable)) (inside.2.trans contactInside.2)⟩
  exact domainEstimate count phase dipoleAngle prepared path index nonterminal hit hitInside radialSmall rotation rotationNorm
    (initial.trans domainToleranceBound) time available patch

end EulerNonuniqueness.Paper
