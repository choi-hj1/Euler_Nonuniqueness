import EulerNonuniqueness.General.QuantitativeFirstContact
import EulerNonuniqueness.Section5.CascadeNormalizedPairCenterDistance
import EulerNonuniqueness.Section5.CascadeFinitePassagePhysicalGap
import EulerNonuniqueness.Section5.CascadeSeparationContact
import EulerNonuniqueness.Section5.CascadePrehitCentroidExtent
import EulerNonuniqueness.Section5.CascadePrehitInternalGap
import EulerNonuniqueness.Section5.UniversalMaterialPassageGap

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_uniform_actual_quantitative_first_separation
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (incomingTime modelSection : ℝ) (modelDerivative : ℝ → ℝ)
    (sectionAfter : incomingTime + 1 < modelSection) (radiusLarge : 512 ≤ separationRadius orbit modelSection)
    (transverse : ∀ time ∈ Icc (modelSection - 1) (modelSection + 1),
      HasDerivAt (separationRadius orbit) (modelDerivative time) time ∧ 1 ≤ modelDerivative time)
    (earlierMargin : ∀ time ≤ modelSection - 1,
      separationRadius orbit time ≤ separationRadius orbit modelSection - 1)
    {factor accuracy : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
    (accuracyPositive : 0 < accuracy) (accuracySmall : accuracy < 1 / 2)
    (referenceSeparated : ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖) :
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
        separationRadius orbit modelSection * changed.length (index.val + 1)) ∧
      |contact - (hit + (modelSection - incomingTime) / omega)| ≤ 2 * accuracy / omega := by
  classical
  let horizon := modelSection + 1 - incomingTime
  have horizonPositive : 0 < horizon := by dsimp only [horizon]; linarith only [sectionAfter]
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨shadowTolerance, shadowPositive, shadowFactory⟩ :=
    exists_universal_material_paper_label_passage_shadowing orbit normalized incomingTime horizon horizonPositive
      accuracy accuracyPositive factorPositive factorOne
  obtain ⟨gapTolerance, gapPositive, gapFactory⟩ :=
    exists_universal_material_paper_label_passage_strict_gap orbit normalized incomingTime horizon horizonPositive
      factorPositive factorOne referenceSeparated
  refine ⟨min shadowTolerance gapTolerance, lt_min shadowPositive gapPositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootPositive boundaryNonnegative
  filter_upwards [shadowFactory scales amplitudePositive ratioBound alphaPositive sectionTime rootPositive boundaryNonnegative,
    gapFactory scales amplitudePositive ratioBound alphaPositive sectionTime rootPositive boundaryNonnegative,
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      thresholdSmall referenceNonnegative,
    scales.eventually_material_prehit_internal_gap amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    eventually_gt_atTop (0 : ℝ)] with frequency shadowEstimate gapEstimate extentEstimate prehitGap frequencyPositive
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
  have lengthPositive : 0 < length := changed.length_pos _
  have initialShadow := initial.trans (min_le_left shadowTolerance gapTolerance)
  have initialGap := initial.trans (min_le_right shadowTolerance gapTolerance)
  have insideWindow {window : ℝ} (endBound : hit + window / omega ≤ path.stop)
      (current : ℝ) (member : current ∈ Icc 0 window) : hit + current / omega ∈ Icc 0 path.stop :=
    ⟨add_nonneg hitInside.1 (div_nonneg member.1 omegaPositive.le),
      (add_le_add_left (div_le_div_of_nonneg_right member.2 omegaPositive.le) hit).trans endBound⟩
  have targetGap (current : ℝ) (member : current ∈ Icc hit (min path.stop endpoint))
      (first second : Fin 4) (different : first ≠ second) :
      factor * length < ‖patchCentroid motion current index first - patchCentroid motion current index second‖ := by
    by_cases atHit : current = hit
    · subst current
      exact (prehitGap prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal hit hitInside.1
        hitInside.2 radialSmall hit ⟨hitInside.1, le_rfl⟩).1 first second different
    have currentPositive : hit < current := lt_of_le_of_ne member.1 (Ne.symm atHit)
    let window := omega * (current - hit)
    have windowPositive : 0 < window := mul_pos omegaPositive (sub_pos.mpr currentPositive)
    have physical : hit + window / omega = current := by dsimp only [window]; field_simp
    have windowBound : window ≤ horizon := by
      have bound : current ≤ hit + horizon / omega := member.2.trans (min_le_right _ _)
      have difference : current - hit ≤ horizon / omega := by linarith only [bound]
      have scaled := (le_div_iff₀ omegaPositive).mp difference
      dsimp only [window]
      nlinarith only [scaled]
    have gaps := gapEstimate count phase dipoleAngle prepared path index hit window windowPositive windowBound rotation rotationNorm
      (insideWindow (by rw [physical]; exact member.2.trans (min_le_left _ _))) initialGap window ⟨windowPositive.le, le_rfl⟩
    have actual := cascadeNormalizedPointPositions_strict_gap_physical changed motion index hit window rotationNorm gaps
      first second different.symm
    change factor * length < ‖patchCentroid motion (hit + window / omega) index first -
      patchCentroid motion (hit + window / omega) index second‖ at actual
    rwa [physical] at actual
  have endpointAvailable : endpoint ≤ path.stop := by
    apply le_of_not_gt
    intro stopBefore
    have premature : path.stop < 1 := stopBefore.trans_le endpointOne
    obtain ⟨other, first, second, different, contact⟩ := path.premature_contact premature
    have stopInside : path.stop ∈ Icc hit (min path.stop endpoint) :=
      ⟨hitInside.2, by rw [min_eq_left stopBefore.le]⟩
    by_cases same : other = index
    · subst other
      have strict := targetGap path.stop stopInside first second different
      rw [contact] at strict
      exact lt_irrefl _ strict
    · have strict := otherGaps other same path.stop stopInside first second different
      rw [contact] at strict
      exact lt_irrefl _ strict
  have shadow (time : ℝ) (member : time ∈ Icc 0 horizon) :
      ‖cascadeNormalizedPointPositions changed motion index hit rotation time -
        centrallySymmetricFourPoint (orbit.positive (time + incomingTime)) (orbit.negative (time + incomingTime))‖ < accuracy :=
    shadowEstimate count phase dipoleAngle prepared path index hit horizon horizonPositive le_rfl rotation rotationNorm
      (insideWindow endpointAvailable) initialShadow time member
  let actual := fun time => pairCenterDistance motion (hit + time / omega) index / length
  let model := fun time => separationRadius orbit (time + incomingTime)
  have actualContinuous : Continuous actual := (prepared.trajectory.movingFamily.pairCenterDistance_continuous index).comp
    (by fun_prop : Continuous (fun time : ℝ => hit + time / omega)) |>.div_const length
  have positiveContinuous : Continuous orbit.positive :=
    continuous_iff_continuousAt.mpr (fun time => (normalized.2.1 time).2.2.1.continuousAt)
  have negativeContinuous : Continuous orbit.negative :=
    continuous_iff_continuousAt.mpr (fun time => (normalized.2.1 time).2.2.2.continuousAt)
  have modelContinuous : Continuous model := ((positiveContinuous.sub negativeContinuous).norm).comp (by fun_prop)
  have modelAtCenter : model (modelSection - incomingTime) = separationRadius orbit modelSection := by
    dsimp only [model]
    congr 1
    ring
  have modelDerivativeAt (time : ℝ) (member : time ∈ Ioo (modelSection - incomingTime - 1) (modelSection - incomingTime + 1)) :
      HasDerivAt model (modelDerivative (time + incomingTime)) time := by
    have localInside : time + incomingTime ∈ Icc (modelSection - 1) (modelSection + 1) := by
      constructor <;> linarith only [member.1, member.2]
    simpa only [mul_one] using (transverse (time + incomingTime) localInside).1.comp time ((hasDerivAt_id time).add_const incomingTime)
  have close (time : ℝ) (member : time ∈ Icc 0 (modelSection - incomingTime + 1)) : |actual time - model time| ≤ 2 * accuracy := by
    have memberHorizon : time ∈ Icc 0 horizon := ⟨member.1, by dsimp only [horizon]; linarith only [member.2]⟩
    have comparison := cascadeNormalizedPointPositions_pair_center_shadow_error changed motion index hit time incomingTime orbit rotationNorm
    exact comparison.trans (mul_le_mul_of_nonneg_left (shadow time memberHorizon).le (by norm_num))
  obtain ⟨fastContact, fastInside, fastValue, fastBefore, fastTiming⟩ := exists_quantitative_first_contact
    (actual := actual) (model := model) (modelDerivative := fun time => modelDerivative (time + incomingTime))
    (initial := 0) (center := modelSection - incomingTime) (halfWidth := 1)
    (level := separationRadius orbit modelSection) (slope := 1) (error := 2 * accuracy)
    (by norm_num) (by linarith only [sectionAfter]) (by norm_num) (by positivity)
    (by linarith only [accuracySmall]) actualContinuous.continuousOn modelContinuous.continuousOn modelAtCenter
    modelDerivativeAt (by
      intro time member
      exact (transverse (time + incomingTime) ⟨by linarith only [member.1], by linarith only [member.2]⟩).2)
    (by
      intro time member
      simpa only [mul_one, sub_zero] using earlierMargin (time + incomingTime) (by linarith only [member.2])) close
  let contact := hit + fastContact / omega
  have fastPositive : 0 < fastContact := by linarith only [fastInside.1, sectionAfter]
  have hitContact : hit < contact := lt_add_of_pos_right hit (div_pos fastPositive omegaPositive)
  have contactInside : contact ∈ Icc (hit + (modelSection - incomingTime - 1) / omega) endpoint := by
    constructor
    · exact add_le_add_left (div_le_div_of_nonneg_right fastInside.1 omegaPositive.le) hit
    · apply add_le_add_left _ hit
      apply div_le_div_of_nonneg_right _ omegaPositive.le
      dsimp only [horizon]
      linarith only [fastInside.2]
  have contactValue : pairCenterDistance motion contact index = separationRadius orbit modelSection * length :=
    (div_eq_iff lengthPositive.ne').mp fastValue
  have prehitPairBound (time : ℝ) (member : time ∈ Icc 0 hit) : pairCenterDistance motion time index ≤ 6 * length := by
    let positions : FourPointConfiguration := fun patch => patchCentroid motion time index patch - quadrupoleCenter motion time index
    have positionsBound : ‖positions‖ ≤ 3 * length := (pi_norm_le_iff_of_nonneg (by positivity)).mpr (by
      intro patch
      exact (extentEstimate prepared path factorSmall index nonterminal hit hitInside.1 hitInside.2 radialSmall time member patch).1)
    have comparison := fourPoint_pair_center_distance_abs_sub_le positions 0
    simp only [Pi.zero_apply, zero_add, zero_div, sub_zero, norm_zero, abs_norm] at comparison
    have identity : ‖(positions 0 + positions 3) / 2 - (positions 1 + positions 2) / 2‖ = pairCenterDistance motion time index := by
      congr 1
      dsimp only [positions, pairCenterDistance]
      ring
    rw [identity] at comparison
    nlinarith only [comparison, positionsBound]
  have earlierStrict (time : ℝ) (member : time ∈ Ico 0 contact) :
      pairCenterDistance motion time index < separationRadius orbit modelSection * length := by
    by_cases beforeHit : time ≤ hit
    · have bound := prehitPairBound time ⟨member.1, beforeHit⟩
      have scaled := mul_le_mul_of_nonneg_right radiusLarge lengthPositive.le
      nlinarith only [bound, scaled, lengthPositive]
    · let fastTime := omega * (time - hit)
      have physical : hit + fastTime / omega = time := by dsimp only [fastTime]; field_simp
      have fastLower : 0 ≤ fastTime := mul_nonneg omegaPositive.le (sub_nonneg.mpr (le_of_not_ge beforeHit))
      have fastUpper : fastTime < fastContact := by
        have bound : time - hit < fastContact / omega := by dsimp only [contact] at member; linarith only [member.2]
        simpa only [fastTime, mul_comm] using (lt_div_iff₀ omegaPositive).mp bound
      have bound := fastBefore fastTime ⟨fastLower, fastUpper⟩
      change pairCenterDistance motion (hit + fastTime / omega) index / length < separationRadius orbit modelSection at bound
      rw [physical] at bound
      exact (div_lt_iff₀ lengthPositive).mp bound
  refine ⟨endpointAvailable, contact, contactInside, ⟨hitInside.1.trans hitContact.le, contactValue, ?_⟩, earlierStrict, ?_⟩
  · intro time nonnegative before
    exact ne_of_lt (earlierStrict time ⟨nonnegative, before⟩)
  · have normalization : contact - (hit + (modelSection - incomingTime) / omega) =
        (fastContact - (modelSection - incomingTime)) / omega := by dsimp only [contact]; ring
    rw [normalization, abs_div, abs_of_pos omegaPositive]
    exact div_le_div_of_nonneg_right (by simpa only [div_one] using fastTiming) omegaPositive.le

end EulerNonuniqueness.Paper

