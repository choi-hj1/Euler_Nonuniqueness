import EulerNonuniqueness.Section5.CascadeMixedFollowerCommonEnvelope
import EulerNonuniqueness.Section5.CascadeFollowerForcingContinuity
import EulerNonuniqueness.Section6.SourcePacketActualOutgoingCommonEnvelopeBudget
import EulerNonuniqueness.General.SwitchedLaplaceWindow

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_mixed_follower_original_prefix_budget :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ tolerance : ℝ, 0 < tolerance →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ drive : Fin count,
    ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ path.stop →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, drive.val < source.val →
      let length := changed.length (source.val + 1)
      0 ≤ entry source ∧ entry source ≤ terminal ∧ 512 ≤ initialDistance source ∧
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
    ∀ finish ∈ Icc 0 terminal, ∀ weight : ℝ, 0 < weight →
    (∀ source : Fin count, drive.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
    ContinuousOn (prepared.followerStrictlyFinerForcing drive) (Icc 0 path.stop) ∧
    ContinuousOn (prepared.coarserFollowerEnvelope drive) (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.followerStrictlyFinerForcing drive time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.coarserFollowerEnvelope drive time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.followerStrictlyFinerForcing drive time) ≤
      incomingConstant * extent ^ 2 * (∑ source ∈ finer,
        changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
          (1 + (changed.location (source.val + 1))⁻¹) * magnitude source /
          (coefficient * changed.omega (source.val + 1)) * Real.exp (-weight * entry source)) +
      outgoingConstant * (∑ source ∈ finer.filter (fun source => entry source < finish),
        changed.circulation (source.val + 1) *
          (changed.circulation (source.val + 1) / weight ^ 2 +
            ((1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
              ‖centroidAsymmetry motion (entry source) source‖) / weight) * Real.exp (-weight * entry source)) +
      tolerance * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.coarserFollowerEnvelope drive time := by
  classical
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, mixedCap, mixedCapPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, mixedFactory⟩ :=
    exists_uniform_actual_mixed_follower_common_envelope
  obtain ⟨continuityCap, continuityCapPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min mixedCap continuityCap
  have capPositive : 0 < rawCap := lt_min mixedCapPositive continuityCapPositive
  have mixedCapBound : rawCap ≤ mixedCap := min_le_left _ _
  have continuityCapBound : rawCap ≤ continuityCap := min_le_right _ _
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    2 * incomingConstant, by positivity, 200000 * outgoingConstant, by positivity, ?_⟩
  intro extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    factorPositive factorSmall rootOne boundaryOne
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [mixedFactory extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
      factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_actual_outgoing_common_envelope_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    scales.eventually_cascade_follower_finer_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans thresholdEighth) referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_gt_atTop (0 : ℝ)] with frequency mixed outgoing regular frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path drive terminal terminalNonnegative terminalBound entry initialDistance direction
  dsimp only
  intro entries extents coefficient coefficientPositive magnitude profiles finish finishInside weight weightPositive rateBounds
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
    ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let sourceAmplitude := fun source => incomingConstant * extent ^ 2 *
    (changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
      (1 + (changed.location (source.val + 1))⁻¹) * magnitude source)
  let sourceSlope := fun source : Fin count => 200000 * outgoingConstant * changed.circulation (source.val + 1) ^ 2
  let sourceConstant := fun source : Fin count => 200000 * outgoingConstant * changed.circulation (source.val + 1) *
    ((1 + initialDistance source) * changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry source) source‖)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have gammaNonnegative (source : Fin count) : 0 ≤ changed.circulation (source.val + 1) :=
    (changed.circulation_pos frequencyPositive ratioPositive _).le
  have coarseContinuous : ContinuousOn (prepared.coarserFollowerEnvelope drive) (Icc 0 path.stop) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro source
    by_cases below : source.val < drive.val
    · simpa only [CascadeSourcePreparedPair.coarserFollowerEnvelope, below, ite_true,
        CascadeSourcePreparedPair.weightedMacroSourceState] using
        (continuousOn_const.mul (stateContinuity prepared capPositive continuityCapBound path source).2.2.2)
    · simpa only [below, ite_false] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 path.stop))
  have forcingContinuous := (regular count phase dipoleAngle prepared path drive).2.1
  have macroInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have coarseInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).coarserFollowerEnvelope = prepared.coarserFollowerEnvelope := by
    funext index time
    simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have forcingInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).followerStrictlyFinerForcing = prepared.followerStrictlyFinerForcing := rfl
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have scalarBounds (source : Fin count) (member : source ∈ finer) :
      0 ≤ entry source ∧ 0 ≤ sourceAmplitude source ∧ 0 ≤ sourceSlope source ∧ 0 ≤ sourceConstant source ∧
        2 * weight ≤ coefficient * changed.omega (source.val + 1) := by
    have below := (Finset.mem_filter.mp member).2
    have initialNonnegative : 0 ≤ initialDistance source := by linarith only [(entries source below).2.2.1]
    have magnitudeNonnegative := (profiles source below).1
    have locationPositive := changed.location_pos (source.val + 1)
    have gamma := gammaNonnegative source
    refine ⟨(entries source below).1, ?_, ?_, ?_, rateBounds source below⟩ <;>
      dsimp only [sourceAmplitude, sourceSlope, sourceConstant] <;> positivity
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : prepared.followerStrictlyFinerForcing drive time ≤
      (∑ source ∈ finer, if time ≤ entry source then sourceAmplitude source *
        Real.exp ((coefficient * changed.omega (source.val + 1)) * (time - entry source))
        else sourceSlope source * (time - entry source) + sourceConstant source) +
        tolerance * prepared.coarserFollowerEnvelope drive time := by
    let completed := Finset.univ.filter (fun source : Fin count => entry source < time)
    have actual := mixed count phase dipoleAngle (prepared.enlargeCap mixedCapBound) path time
      ⟨inside.1, inside.2.trans (finishInside.2.trans terminalBound)⟩ drive completed entry initialDistance direction
      (fun source done below => by
        have prior := (Finset.mem_filter.mp done).2
        rcases entries source below with ⟨nonnegative, _, large, small, unit, first, second, projection, upper⟩
        exact ⟨nonnegative, prior.le, large, small, unit, first, second, projection, upper⟩)
      (fun source below notDone => extents source below time ⟨inside.1, le_of_not_gt (by
        simpa only [completed, Finset.mem_filter, Finset.mem_univ, true_and] using notDone)⟩)
    simp only [forcingInvariant, coarseInvariant, rawInvariant] at actual
    dsimp only [CascadeSourcePreparedPair.enlargeCap] at actual
    have finiteBound : outgoingConstant * (∑ source ∈ finer.filter (fun source => source ∈ completed),
        changed.circulation (source.val + 1) * (4 * ‖centroidAsymmetry motion time source‖ +
          changed.length (source.val + 1) * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
            changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)) +
        incomingConstant * extent ^ 2 * (∑ source ∈ finer.filter (fun source => source ∉ completed),
          changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
            (1 + (changed.location (source.val + 1))⁻¹) * sharpState source time) ≤
        ∑ source ∈ finer, if time ≤ entry source then sourceAmplitude source *
          Real.exp ((coefficient * changed.omega (source.val + 1)) * (time - entry source))
          else sourceSlope source * (time - entry source) + sourceConstant source := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_ite]
      apply Finset.sum_le_sum
      intro source member
      have below := (Finset.mem_filter.mp member).2
      by_cases done : source ∈ completed
      · have prior := (Finset.mem_filter.mp done).2
        rcases entries source below with ⟨nonnegative, entryBound, large, small, unit, first, second, projection, upper⟩
        have duration : 0 ≤ terminal - entry source := sub_nonneg.mpr entryBound
        have actualEnvelope := outgoing count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path source
          (entry source) (terminal - entry source) (initialDistance source) nonnegative duration
          (by linarith only [terminalBound]) large small (direction source) unit first second projection upper
        have elapsed : time - entry source ∈ Icc 0 (terminal - entry source) :=
          ⟨(sub_pos.mpr prior).le, by linarith only [inside.2, finishInside.2]⟩
        have affine := actualEnvelope.2 (time - entry source) elapsed
        have shifted : entry source + (time - entry source) = time := by ring
        simp only [shifted] at affine
        have initialNonnegative : 0 ≤ initialDistance source := by linarith only [large]
        have extra : changed.length (source.val + 1) ^ 2 ≤
            (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
              ‖centroidAsymmetry motion (entry source) source‖ := by
          nlinarith only [mul_nonneg initialNonnegative (sq_nonneg (changed.length (source.val + 1))), norm_nonneg (centroidAsymmetry motion (entry source) source)]
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
        convert scaled using 1 <;> dsimp only [sourceSlope, sourceConstant] <;> ring
      · have later : time ≤ entry source := le_of_not_gt (by
          simpa only [completed, Finset.mem_filter, Finset.mem_univ, true_and] using done)
        have scaled := mul_le_mul_of_nonneg_left ((profiles source below).2 time ⟨inside.1, later⟩)
          (show 0 ≤ incomingConstant * extent ^ 2 * (changed.circulation (source.val + 1) *
            changed.length (source.val + 1) ^ 2 * (1 + (changed.location (source.val + 1))⁻¹)) by
            have locationPositive := changed.location_pos (source.val + 1)
            have gamma := gammaNonnegative source
            positivity)
        simp only [done, ite_false, later, ite_true]
        convert scaled using 1 <;> dsimp only [sourceAmplitude, sharpState] <;> ring
    exact actual.trans (add_le_add_right finiteBound _)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop :=
    Icc_subset_Icc le_rfl (finishInside.2.trans terminalBound)
  have bound := intervalIntegral.integral_exp_neg_mul_le_of_finite_switched_majorant finer entry sourceAmplitude
    (fun source => coefficient * changed.omega (source.val + 1)) sourceSlope sourceConstant
    (forcingContinuous.mono subset) (coarseContinuous.mono subset) finishInside.1 weightPositive tolerancePositive.le
    scalarBounds pointwise
  refine ⟨forcingContinuous, coarseContinuous, bound.1, bound.2.1, bound.2.2.trans_eq ?_⟩
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro source _
    dsimp only [sourceAmplitude]
    ring
  · apply Finset.sum_congr rfl
    intro source _
    dsimp only [sourceSlope, sourceConstant]
    ring

end EulerNonuniqueness.Paper
