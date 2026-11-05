import EulerNonuniqueness.Section5.CascadeMixedForeignPatchEnvelope
import EulerNonuniqueness.Section5.CascadeMixedSelectedFinerOriginalPrefixBudget
import EulerNonuniqueness.Section5.CascadeForeignCoefficientSeriesContinuity
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
theorem exists_uniform_actual_mixed_foreign_patch_original_prefix_budget :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ coarseConstant ≥ (0 : ℝ), ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ tolerance : ℝ, 0 < tolerance →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ receiver : Fin count,
    ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ path.stop →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, receiver.val < source.val →
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
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source),
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
    (∀ source : Fin count, receiver.val < source.val → 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
        magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    ∀ finish ∈ Icc 0 terminal, ∀ weight : ℝ, 0 < weight →
    (∀ source : Fin count, receiver.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let ownForcing := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid motion current receiver patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) ownRadius (power + 1) time‖
    let coarseMask := fun time => ‖fun source : Fin count => if source.val ≤ receiver.val then
      changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖
    ContinuousOn ownForcing (Icc 0 path.stop) ∧ ContinuousOn coarseMask (Icc 0 path.stop) ∧
    ContinuousOn (fun time => prepared.macroSourceState time receiver) (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * ownForcing time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * coarseMask time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.macroSourceState time receiver) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ownForcing time) ≤
      (coarseConstant / changed.location (receiver.val + 1) ^ 4) * (216360000 * changed.hessian + 576 * changed.strain) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * coarseMask time) +
      prepared.mixedSelectedFinerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient
        entry initialDistance magnitude weight finish +
      tolerance * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.macroSourceState time receiver) := by
  classical
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, mixedCap, mixedCapPositive,
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, mixedFactory⟩ :=
    exists_uniform_actual_mixed_foreign_patch_envelope
  let outgoingConstant : ℝ := 8000000000
  have outgoingNonnegative : 0 ≤ outgoingConstant := by norm_num [outgoingConstant]
  obtain ⟨continuityCap, continuityCapPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min mixedCap continuityCap
  have capPositive : 0 < rawCap := lt_min mixedCapPositive continuityCapPositive
  have mixedCapBound : rawCap ≤ mixedCap := min_le_left _ _
  have continuityCapBound : rawCap ≤ continuityCap := min_le_right _ _
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    coarseConstant, coarseNonnegative, 2 * incomingConstant, by positivity, 200000 * outgoingConstant, by positivity, ?_⟩
  intro extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    factorPositive factorSmall rootOne boundaryOne
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [mixedFactory extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
      factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_actual_outgoing_common_envelope_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    scales.eventually_cascade_foreign_coefficient_series_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans thresholdEighth) referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with frequency mixed outgoing regular lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver terminal terminalNonnegative terminalBound entry initialDistance direction
  dsimp only
  intro entries extents coefficient coefficientPositive magnitude profiles finish finishInside weight weightPositive rateBounds
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let finer := Finset.univ.filter (fun source : Fin count => receiver.val < source.val)
  let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
  let forcing := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => patchCentroid motion current receiver patch) ownRadius (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) ownRadius (power + 1) time‖
  let coarseMask := fun time => ‖fun source : Fin count => if source.val ≤ receiver.val then changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖
  let coarseCoefficient := coarseConstant / changed.location (receiver.val + 1) ^ 4 * (216360000 * changed.hessian + 576 * changed.strain)
  let adjusted := fun time => forcing time - coarseCoefficient * coarseMask time
  let gap := fun source : Fin count => |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
    ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let sourceAmplitude := fun source => incomingConstant * extent ^ 2 *
    (changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 /
      gap source ^ 4 * (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * magnitude source)
  let sourceSlope := fun source : Fin count => (200000 * outgoingConstant / changed.location (receiver.val + 1) ^ 4) * changed.circulation (source.val + 1) ^ 2
  let sourceConstant := fun source : Fin count => (200000 * outgoingConstant / changed.location (receiver.val + 1) ^ 4) * changed.circulation (source.val + 1) *
    ((1 + initialDistance source) * changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry source) source‖)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have receiverLocationPositive : 0 < changed.location (receiver.val + 1) := changed.location_pos _
  have gammaNonnegative (source : Fin count) : 0 ≤ changed.circulation (source.val + 1) := (changed.circulation_pos frequencyPositive ratioPositive _).le
  have macroContinuous := (stateContinuity prepared capPositive continuityCapBound path receiver).2.2.2
  have coarseContinuous : ContinuousOn coarseMask (Icc 0 path.stop) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro source
    by_cases selected : source.val ≤ receiver.val
    · simpa only [coarseMask, selected, ite_true] using
        ((continuousOn_const : ContinuousOn (fun _ : ℝ => changed.location (source.val + 1) ^ 4) (Icc 0 path.stop)).mul
          (stateContinuity prepared capPositive continuityCapBound path source).2.2.2)
    · simpa only [coarseMask, selected, ite_false] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 path.stop))
  have radiusNonnegative : 0 ≤ ownRadius := mul_nonneg (by positivity) (changed.length_pos _).le
  have radiusSmall : ownRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) := by
    have lengthSmall : changed.length (receiver.val + 1) ≤ changed.location (receiver.val + 1) := by simpa only [one_mul] using (lengths (receiver.val + 1)).le
    calc
      _ ≤ factor / 39321600 * changed.location (receiver.val + 1) := mul_le_mul_of_nonneg_left lengthSmall (by positivity)
      _ ≤ (1 : ℝ) / 39321600 * changed.location (receiver.val + 1) := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right factorOne (by norm_num)) receiverLocationPositive.le
      _ ≤ _ := by
        change (1 : ℝ) / 39321600 * changed.location (receiver.val + 1) ≤ changed.location (receiver.val + 1) / (100000 * 96)
        nlinarith only [receiverLocationPositive]
  have regularData := regular count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver ownRadius radiusNonnegative radiusSmall
  have forcingContinuous : ContinuousOn forcing (Icc 0 path.stop) :=
    continuousOn_finset_sum Finset.univ (fun patch _ => (regularData.1 patch).2)
  have macroInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) : (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have centerInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
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
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : adjusted time ≤
      (∑ source ∈ finer, if time ≤ entry source then sourceAmplitude source *
        Real.exp ((coefficient * changed.omega (source.val + 1)) * (time - entry source))
        else sourceSlope source * (time - entry source) + sourceConstant source) +
        tolerance * prepared.macroSourceState time receiver := by
    let completed := Finset.univ.filter (fun source : Fin count => entry source < time)
    have actual := mixed count phase dipoleAngle (prepared.enlargeCap mixedCapBound) path time
      ⟨inside.1, inside.2.trans (finishInside.2.trans terminalBound)⟩ receiver completed entry initialDistance direction
      (fun source done below => by
        have prior := (Finset.mem_filter.mp done).2
        rcases entries source below with ⟨nonnegative, _, large, small, unit, first, second, projection, upper⟩
        exact ⟨nonnegative, prior.le, large, small, unit, first, second, projection, upper⟩)
      (fun source below notDone => extents source below time ⟨inside.1, le_of_not_gt (by
        simpa only [completed, Finset.mem_filter, Finset.mem_univ, true_and] using notDone)⟩)
    dsimp only at actual
    have actualBound := actual.2.2
    simp only [macroInvariant, centerInvariant, rawInvariant] at actualBound
    dsimp only [CascadeSourcePreparedPair.enlargeCap] at actualBound
    change forcing time ≤ coarseCoefficient * coarseMask time + incomingConstant * extent ^ 2 *
      (∑ source ∈ finer.filter (fun source => source ∉ completed),
        changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
          (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * sharpState source time) +
      (outgoingConstant / changed.location (receiver.val + 1) ^ 4) *
        (∑ source ∈ finer.filter (fun source => source ∈ completed),
          changed.circulation (source.val + 1) * (4 * ‖centroidAsymmetry motion time source‖ +
            changed.length (source.val + 1) * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
              changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)) +
      tolerance * prepared.macroSourceState time receiver at actualBound
    have finiteBound : (outgoingConstant / changed.location (receiver.val + 1) ^ 4) * (∑ source ∈ finer.filter (fun source => source ∈ completed),
        changed.circulation (source.val + 1) * (4 * ‖centroidAsymmetry motion time source‖ +
          changed.length (source.val + 1) * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
            changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)) +
        incomingConstant * extent ^ 2 * (∑ source ∈ finer.filter (fun source => source ∉ completed),
          changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
            (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * sharpState source time) ≤
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
        have scaled := mul_le_mul_of_nonneg_left scalar
          (mul_nonneg (div_nonneg outgoingNonnegative (pow_nonneg receiverLocationPositive.le 4)) (gammaNonnegative source))
        simp only [done, ite_true, not_le.mpr prior, ite_false]
        convert scaled using 1 <;> dsimp only [sourceSlope, sourceConstant] <;> ring
      · have later : time ≤ entry source := le_of_not_gt (by
          simpa only [completed, Finset.mem_filter, Finset.mem_univ, true_and] using done)
        have scaled := mul_le_mul_of_nonneg_left ((profiles source below).2 time ⟨inside.1, later⟩)
          (show 0 ≤ incomingConstant * extent ^ 2 * (changed.circulation (source.val + 1) *
            changed.length (source.val + 1) ^ 2 / gap source ^ 4 * (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1))) by
            have locationPositive := changed.location_pos (source.val + 1)
            have gamma := gammaNonnegative source
            positivity)
        simp only [done, ite_false, later, ite_true]
        convert scaled using 1 <;> dsimp only [sourceAmplitude, sharpState] <;> ring
    have sumBound := add_le_add_right finiteBound (tolerance * prepared.macroSourceState time receiver)
    dsimp only [adjusted]
    linarith only [actualBound, sumBound]
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl (finishInside.2.trans terminalBound)
  have bound := intervalIntegral.integral_exp_neg_mul_le_of_finite_switched_majorant finer entry sourceAmplitude
    (fun source => coefficient * changed.omega (source.val + 1)) sourceSlope sourceConstant
    ((forcingContinuous.sub ((continuousOn_const : ContinuousOn (fun _ : ℝ => coarseCoefficient) (Icc 0 path.stop)).mul coarseContinuous)).mono subset)
    (macroContinuous.mono subset) finishInside.1 weightPositive tolerancePositive.le
    scalarBounds pointwise
  have exponential : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have forcingI := (exponential.continuousOn.mul (forcingContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have coarseI := (exponential.continuousOn.mul (coarseContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have budgetIdentity : (∑ source ∈ finer, (2 * sourceAmplitude source / (coefficient * changed.omega (source.val + 1))) * Real.exp (-weight * entry source)) +
      (∑ source ∈ finer.filter (fun source => entry source < finish),
        (sourceSlope source / weight ^ 2 + sourceConstant source / weight) * Real.exp (-weight * entry source)) =
      prepared.mixedSelectedFinerSourcePrefixBudget receiver (2 * incomingConstant) (200000 * outgoingConstant) extent coefficient
        entry initialDistance magnitude weight finish := by
    dsimp only [CascadeSourcePreparedPair.mixedSelectedFinerSourcePrefixBudget]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl; intro source _; dsimp only [sourceAmplitude]; ring
    · apply Finset.sum_congr rfl; intro source _; dsimp only [sourceSlope, sourceConstant]; ring
  have integralIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * adjusted time) =
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time) -
        coarseCoefficient * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * coarseMask time := by
    dsimp only [adjusted]; simp_rw [mul_sub, mul_left_comm (Real.exp _) coarseCoefficient]
    rw [intervalIntegral.integral_sub forcingI (coarseI.const_mul coarseCoefficient), intervalIntegral.integral_const_mul]
  refine ⟨forcingContinuous, coarseContinuous, macroContinuous, forcingI, coarseI, bound.2.1, ?_⟩
  have result := bound.2.2
  rw [integralIdentity, budgetIdentity] at result
  change (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time) ≤
    coarseCoefficient * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * coarseMask time) +
      prepared.mixedSelectedFinerSourcePrefixBudget receiver (2 * incomingConstant) (200000 * outgoingConstant) extent coefficient
        entry initialDistance magnitude weight finish +
      tolerance * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.macroSourceState time receiver)
  linarith only [result]
end EulerNonuniqueness.Paper
