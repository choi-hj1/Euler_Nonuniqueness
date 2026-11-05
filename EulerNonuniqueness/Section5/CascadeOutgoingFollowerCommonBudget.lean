import EulerNonuniqueness.Section5.CascadeOutgoingSingletonCommonEnvelope
import EulerNonuniqueness.Section5.CascadeFollowerCommonSourceEnvelope
import EulerNonuniqueness.Section5.CascadeFollowerForcingContinuity
import EulerNonuniqueness.Section6.SourcePacketActualOutgoingCommonEnvelopeSubwindow

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem weighted_common_source_action
    {envelope : ℝ → ℝ} {factor length cost start finish weight : ℝ}
    (factorNonnegative : 0 ≤ factor) (ordered : start ≤ finish) (weightPositive : 0 < weight)
    (envelopeI : IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) * envelope time) volume start finish)
    (envelopeBound : (∫ time in start..finish, Real.exp (-weight * (time - start)) * envelope time) ≤ 100000 * cost)
    (constantCost : length ^ 2 / weight ≤ cost) :
    IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) * (factor * (envelope time + length ^ 2))) volume start finish ∧
    (∫ time in start..finish, Real.exp (-weight * (time - start)) * (factor * (envelope time + length ^ 2))) ≤
      200000 * factor * cost := by
  have constantData := intervalIntegral.integral_exp_neg_mul_le_of_affine_majorant
    (function := fun _ : ℝ => length ^ 2) (weight := weight) (slope := 0) (constant := length ^ 2)
    (origin := start) (start := start) (finish := finish) continuousOn_const weightPositive (by norm_num)
    (sq_nonneg length) le_rfl ordered (fun _ _ => by simp only [zero_mul, zero_add, le_refl])
  have constantBound : (∫ time in start..finish, Real.exp (-weight * (time - start)) * length ^ 2) ≤ length ^ 2 / weight := by
    simpa only [zero_div, zero_mul, zero_add] using constantData.2
  have identity : (fun time => Real.exp (-weight * (time - start)) * (factor * (envelope time + length ^ 2))) =
      (fun time => factor * (Real.exp (-weight * (time - start)) * envelope time + Real.exp (-weight * (time - start)) * length ^ 2)) := by
    funext time
    ring
  rw [identity]
  refine ⟨(envelopeI.add constantData.1).const_mul factor, ?_⟩
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add envelopeI constantData.1]
  have costNonnegative := (div_nonneg (sq_nonneg length) weightPositive.le).trans constantCost
  have total : (∫ time in start..finish, Real.exp (-weight * (time - start)) * envelope time) +
      (∫ time in start..finish, Real.exp (-weight * (time - start)) * length ^ 2) ≤ 200000 * cost := by
    linarith only [envelopeBound, constantBound, constantCost, costNonnegative]
  exact (mul_le_mul_of_nonneg_left total factorNonnegative).trans_eq (by ring)

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_actual_outgoing_follower_common_budget :
    ∃ thresholdRadius > (0 : ℝ), thresholdRadius ≤ 1 / 8 ∧ ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdRadius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {cap shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ drive : Fin count,
    ∀ start finish : ℝ, 0 ≤ start → start ≤ finish → finish ≤ path.stop →
    ∀ entryTime initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, drive.val < source.val →
      let length := changed.length (source.val + 1)
      0 ≤ entryTime source ∧ entryTime source ≤ start ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entryTime source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion (entryTime source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entryTime source) source - secondDipoleCenter motion (entryTime source) source)).re ∧
      ‖firstDipoleCenter motion (entryTime source) source - secondDipoleCenter motion (entryTime source) source‖ ≤
        (5 / 4 : ℝ) * length * initialDistance source) →
    ∀ weight : ℝ, 0 < weight →
    ContinuousOn (prepared.followerStrictlyFinerForcing drive) (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) * prepared.followerStrictlyFinerForcing drive time) volume start finish ∧
    (∫ time in start..finish, Real.exp (-weight * (time - start)) * prepared.followerStrictlyFinerForcing drive time) ≤
      constant * ∑ source ∈ Finset.univ.filter (fun source : Fin count => drive.val < source.val),
        changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) / weight ^ 2 +
          (changed.circulation (source.val + 1) * (start - entryTime source) +
            (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entryTime source) source‖) / weight) := by
  obtain ⟨thresholdRadius, thresholdPositive, thresholdSmall, singletonConstant, singletonNonnegative, singletons⟩ :=
    exists_actual_outgoing_singleton_common_envelope
  refine ⟨thresholdRadius, thresholdPositive, thresholdSmall, 200000 * singletonConstant, by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [singletons scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_actual_outgoing_common_envelope_subwindow amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    scales.eventually_cascade_follower_finer_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans thresholdSmall) referenceNonnegative rootOne boundaryOne factorPositive factorOne, eventually_gt_atTop (0 : ℝ)]
    with frequency singletons subwindows continuous frequencyPositive
  intro count phase dipoleAngle cap shapeRadius monitor prepared path drive start finish startNonnegative ordered finishBound entryTime initialDistance direction
  dsimp only
  intro entries weight weightPositive
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let sources := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  let envelope := fun (source : Fin count) time => 4 * ‖centroidAsymmetry motion time source‖ +
    changed.length (source.val + 1) * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ + changed.radius (source.val + 1) ^ 2
  let commonSource := fun (source : Fin count) time => singletonConstant * changed.circulation (source.val + 1) *
    (envelope source time + changed.length (source.val + 1) ^ 2)
  let cost := fun source : Fin count => changed.circulation (source.val + 1) / weight ^ 2 +
    (changed.circulation (source.val + 1) * (start - entryTime source) + (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
      ‖centroidAsymmetry motion (entryTime source) source‖) / weight
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have circulationPositive (source : Fin count) : 0 < changed.circulation (source.val + 1) := changed.circulation_pos frequencyPositive ratioPositive _
  have commonNonnegative (source : Fin count) (time : ℝ) : 0 ≤ commonSource source time := by
    have lengthPositive := changed.length_pos (source.val + 1)
    have circulation := circulationPositive source
    dsimp only [commonSource, envelope]
    positivity
  have pointwise (time : ℝ) (inside : time ∈ Icc start finish) : prepared.followerStrictlyFinerForcing drive time ≤
      ∑ source ∈ sources, commonSource source time := by
    apply prepared.followerStrictlyFinerForcing_le_common_source_envelope drive time (fun source => commonSource source time)
      (fun source _ => commonNonnegative source time)
    intro receiver follower source finer
    obtain ⟨entryNonnegative, entryBound, initialLarge, initialSmall, directionNorm, firstInitial, secondInitial, initialProjection, initialUpper⟩ := entries source finer
    have horizonNonnegative : 0 ≤ finish - entryTime source := by linarith only [entryBound, ordered]
    have endBound : entryTime source + (finish - entryTime source) ≤ path.stop := by linarith only [finishBound]
    have elapsedInside : time - entryTime source ∈ Icc 0 (finish - entryTime source) :=
      ⟨by linarith only [entryBound, inside.1], by linarith only [inside.2]⟩
    have actual := singletons count phase dipoleAngle prepared path receiver source (by omega) (entryTime source) (finish - entryTime source)
      (initialDistance source) entryNonnegative horizonNonnegative endBound initialLarge initialSmall (direction source) directionNorm
      firstInitial secondInitial initialProjection initialUpper (time - entryTime source) elapsedInside
    have shifted : entryTime source + (time - entryTime source) = time := by ring
    simpa only [commonSource, envelope, shifted, mul_assoc] using actual.2.2.2
  have sourceAction (source : Fin count) (finer : drive.val < source.val) :
      IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) * commonSource source time) volume start finish ∧
      (∫ time in start..finish, Real.exp (-weight * (time - start)) * commonSource source time) ≤
        (200000 * singletonConstant) * (changed.circulation (source.val + 1) * cost source) := by
    obtain ⟨entryNonnegative, entryBound, initialLarge, initialSmall, directionNorm, firstInitial, secondInitial, initialProjection, initialUpper⟩ := entries source finer
    have horizonNonnegative : 0 ≤ finish - entryTime source := by linarith only [entryBound, ordered]
    have endBound : entryTime source + (finish - entryTime source) ≤ path.stop := by linarith only [finishBound]
    have actual := subwindows count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path source (entryTime source) (finish - entryTime source)
      (initialDistance source) entryNonnegative horizonNonnegative endBound initialLarge initialSmall (direction source) directionNorm
      firstInitial secondInitial initialProjection initialUpper
    have window := actual.2 start ⟨entryBound, by linarith only [ordered]⟩ finish ⟨ordered, by linarith⟩ weight weightPositive
    change IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) * envelope source time) volume start finish ∧
      (∫ time in start..finish, Real.exp (-weight * (time - start)) * envelope source time) ≤ 100000 * cost source at window
    have constantCost : changed.length (source.val + 1) ^ 2 / weight ≤ cost source := by
      have delayNonnegative := mul_nonneg (circulationPositive source).le (sub_nonneg.mpr entryBound)
      have initialNonnegative : 0 ≤ initialDistance source := by linarith only [initialLarge]
      have initialProduct := mul_nonneg initialNonnegative (sq_nonneg (changed.length (source.val + 1)))
      have numerator : changed.length (source.val + 1) ^ 2 ≤ changed.circulation (source.val + 1) * (start - entryTime source) +
          (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entryTime source) source‖ := by
        nlinarith only [delayNonnegative, initialProduct, norm_nonneg (centroidAsymmetry motion (entryTime source) source)]
      exact (div_le_div_of_nonneg_right numerator weightPositive.le).trans
        (le_add_of_nonneg_left (div_nonneg (circulationPositive source).le (sq_nonneg weight)))
    have bound := weighted_common_source_action (mul_nonneg singletonNonnegative (circulationPositive source).le) ordered weightPositive window.1 window.2 constantCost
    simpa only [commonSource, mul_assoc] using bound
  have continuousData := continuous count phase dipoleAngle prepared path drive
  have forcingI := continuousData.2.2 start finish startNonnegative ordered finishBound weight
  have sumI : IntervalIntegrable (fun time => ∑ source ∈ sources, Real.exp (-weight * (time - start)) * commonSource source time) volume start finish := by
    have summed := IntervalIntegrable.sum (s := sources)
      (f := fun source time => Real.exp (-weight * (time - start)) * commonSource source time)
      (fun source member => (sourceAction source (Finset.mem_filter.mp member).2).1)
    convert summed using 1
    funext time
    simp only [Finset.sum_apply]
  refine ⟨continuousData.2.1, forcingI, ?_⟩
  calc
    _ ≤ ∫ time in start..finish, ∑ source ∈ sources, Real.exp (-weight * (time - start)) * commonSource source time :=
      intervalIntegral.integral_mono_on ordered forcingI sumI (fun time inside => by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
    _ = ∑ source ∈ sources, ∫ time in start..finish, Real.exp (-weight * (time - start)) * commonSource source time :=
      intervalIntegral.integral_finset_sum (fun source member => (sourceAction source (Finset.mem_filter.mp member).2).1)
    _ ≤ ∑ source ∈ sources, (200000 * singletonConstant) * (changed.circulation (source.val + 1) * cost source) :=
      Finset.sum_le_sum (fun source member => (sourceAction source (Finset.mem_filter.mp member).2).2)
    _ = _ := (Finset.mul_sum _ _ _).symm

end EulerNonuniqueness.Paper
