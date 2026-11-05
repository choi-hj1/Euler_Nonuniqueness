import EulerNonuniqueness.Section5.CascadeGivenMapStrongFollowerDrivenResponse
import EulerNonuniqueness.Section5.CascadeMixedFollowerResolvedSourceEnvelope

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_given_map_strong_follower_prefix_resolved_source_envelope
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
    ∃ comparisonConstant ≥ (1 : ℝ), ∃ geometryConstant ≥ (1 : ℝ), ∃ rowConstant ≥ (0 : ℝ),
    ∃ ratioMin ≥ max 2 (2 * constant), ∃ rootMin ≥ (8 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ tolerance : ℝ, 0 < tolerance →
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant : ℝ), 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ drive : Fin count, drive.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, drive.val < source.val →
      let length := changed.length (source.val + 1)
      0 ≤ entry source ∧ entry source ≤ path.stop ∧ 512 ≤ initialDistance source ∧
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
    (∀ source : Fin count, drive.val < source.val → 0 ≤ magnitude source ∧ ∀ time ∈ Icc 0 (entry source),
      sharpState source time ≤ magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time receiver| + |stableShape motion time receiver| ≤ radius) →
    ∃ lift : Fin count → Fin 2 → ℝ → ℝ,
      (∀ receiver side, Continuous (lift receiver side) ∧ lift receiver side 0 = phase (receiver.val + 1)) ∧
      (∀ receiver : Fin count, receiver.val < drive.val → ∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
            Complex.exp (Complex.I * (lift receiver side time : ℂ))) ∧
      let envelope := fun time => ‖fun receiver : Fin count => if receiver.val < drive.val then
        changed.location (receiver.val + 1) ^ 4 * (prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
          ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) else 0‖
      let driver := fun time => prepared.weightedMacroSourceState time drive
      let remaining := prepared.followerStrictlyFinerForcing drive
      let rho := 216360000 * changed.hessian + 576 * changed.strain
      let growth := constant * changed.omega (drive.val + 1) / changed.ratio
      let multiplier := comparisonConstant * constant
      let feedback := rowConstant * geometryConstant * rho + tolerance * geometryConstant
      let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
      let sourceEnvelope := fun time => ∑ source ∈ finer,
        if time ≤ entry source then
          incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
            (1 + (changed.location (source.val + 1))⁻¹) * magnitude source *
              Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))
        else outgoingConstant * changed.circulation (source.val + 1) *
          (changed.circulation (source.val + 1) * (time - entry source) +
            (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
              ‖centroidAsymmetry motion (entry source) source‖)
      ContinuousOn envelope (Icc 0 finish) ∧ ContinuousOn driver (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
      IntervalIntegrable envelope volume 0 finish ∧ IntervalIntegrable driver volume 0 finish ∧
      IntervalIntegrable remaining volume 0 finish ∧ envelope 0 = 0 ∧
      (∀ time ∈ Icc 0 finish, prepared.coarserFollowerEnvelope drive time ≤ geometryConstant * envelope time) ∧
      (∀ time ∈ Icc 0 finish, 0 ≤ sourceEnvelope time ∧
        remaining time ≤ sourceEnvelope time + tolerance * (geometryConstant * envelope time)) ∧
      IntervalIntegrable sourceEnvelope volume 0 finish ∧
      ∀ time ∈ Icc 0 finish,
        IntervalIntegrable (fun current => Real.exp ((growth + multiplier * feedback) * (time - current)) *
          (rowConstant * rho * driver current + sourceEnvelope current)) volume 0 time ∧
        envelope time ≤ multiplier * ∫ current in (0 : ℝ)..time,
          Real.exp ((growth + multiplier * feedback) * (time - current)) *
            (rowConstant * rho * driver current + sourceEnvelope current) := by
  classical
  obtain ⟨drivenThreshold, drivenPositive, drivenEighth, drivenCap, drivenCapPositive, drivenFactory⟩ :=
    exists_uniform_actual_given_map_strong_follower_driven_response graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨sourceThreshold, sourcePositive, _, sourceCap, sourceCapPositive, incomingConstant, incomingNonnegative,
    outgoingBase, outgoingBaseNonnegative, sourceFactory⟩ := exists_uniform_actual_mixed_follower_common_envelope
  let outgoingConstant := 200000 * outgoingBase
  have outgoingNonnegative : 0 ≤ outgoingConstant := by dsimp only [outgoingConstant]; positivity
  obtain ⟨geometryRadius, geometryRadiusPositive, _, freshGeometry, freshGeometryOne, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let rawCap := min drivenCap sourceCap
  let thresholdMax := min drivenThreshold sourceThreshold
  have capPositive : 0 < rawCap := lt_min drivenCapPositive sourceCapPositive
  have capDriven : rawCap ≤ drivenCap := min_le_left _ _
  have capSource : rawCap ≤ sourceCap := min_le_right _ _
  refine ⟨thresholdMax, lt_min drivenPositive sourcePositive, (min_le_left _ _).trans drivenEighth,
    rawCap, capPositive, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨drivenRadius, drivenRadiusPositive, drivenQuarter, constant, constantOne, comparisonConstant, comparisonOne,
    drivenGeometry, drivenGeometryOne, rowConstant, rowNonnegative, drivenRoot, drivenRootEight, drivenParameters⟩ :=
    drivenFactory factorPositive factorSmall
  let radius := min drivenRadius geometryRadius
  let geometryConstant := max drivenGeometry freshGeometry
  let ratioMin := max 2 (2 * constant)
  let rootMin := drivenRoot
  have geometryOne : 1 ≤ geometryConstant := drivenGeometryOne.trans (le_max_left _ _)
  have geometryNonnegative : 0 ≤ geometryConstant := zero_le_one.trans geometryOne
  have multiplierNonnegative : 0 ≤ comparisonConstant * constant := by positivity
  refine ⟨radius, lt_min drivenRadiusPositive geometryRadiusPositive,
    (min_le_left _ _).trans drivenQuarter, constant, constantOne, comparisonConstant, comparisonOne,
    geometryConstant, geometryOne, rowConstant, rowNonnegative, ratioMin, le_rfl, rootMin,
    drivenRootEight, ?_⟩
  intro extent extentOne tolerance tolerancePositive scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant boundaryOne
  have drivenRatio : max 2 (2 * constant) ≤ scales.ratio := ratioLarge
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans drivenRatio
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans
    (drivenRootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := (thresholdBound.trans (min_le_left _ _)).trans drivenEighth
  filter_upwards [drivenParameters scales scaleRoot rootLarge amplitudeIdentity drivenRatio alphaPositive
      threshold referenceConstant boundaryConstant (thresholdBound.trans (min_le_left _ _)) referenceNonnegative boundaryOne orbit sectionTime,
    sourceFactory extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans (min_le_right _ _))
      orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_actual_outgoing_common_envelope_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive (factorSmall.trans (by norm_num)) (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    geometries scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive (factorSmall.trans (by norm_num)) thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    eventually_gt_atTop (0 : ℝ)] with frequency drivenEstimate mixed outgoing geometryEstimate coherence frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path drive nonterminal finish finishNonnegative finishBound entry initialDistance direction
  dsimp only
  intro entries extents coefficient coefficientPositive magnitude profiles small
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let envelopeOf := fun (chosen : Fin count → Fin 2 → ℝ → ℝ) time => ‖fun receiver : Fin count =>
    if receiver.val < drive.val then changed.location (receiver.val + 1) ^ 4 *
      (prepared.finiteCoordinateSize graph coordinate (chosen receiver) receiver time +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) else 0‖
  let driver := fun time => prepared.weightedMacroSourceState time drive
  let remaining := prepared.followerStrictlyFinerForcing drive
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let growth := constant * changed.omega (drive.val + 1) / changed.ratio
  let multiplier := comparisonConstant * constant
  let feedback := rowConstant * geometryConstant * rho + tolerance * geometryConstant
  let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  let sourceEnvelope := fun time => ∑ source ∈ finer,
    if time ≤ entry source then incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
      (1 + (changed.location (source.val + 1))⁻¹) * magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))
    else outgoingConstant * changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) * (time - entry source) +
      (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry source) source‖)
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have macroInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have envelopeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).coarserFollowerEnvelope = prepared.coarserFollowerEnvelope := by
    funext index time
    simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have driverInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).weightedMacroSourceState = prepared.weightedMacroSourceState := by
    funext time source
    simp only [CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have remainingInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).followerStrictlyFinerForcing = prepared.followerStrictlyFinerForcing := rfl
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize = prepared.finiteCoordinateSize := rfl
  obtain ⟨lift, liftProperties, liftPolar, drivenData⟩ := drivenEstimate count phase dipoleAngle (prepared.enlargeCap capDriven) path
    drive nonterminal finish finishNonnegative finishBound
      (fun receiver below time inside => (small receiver below time inside).trans (min_le_left _ _))
  dsimp only at drivenData
  simp only [rawInvariant, sizeInvariant, driverInvariant, remainingInvariant] at drivenData
  let envelope := envelopeOf lift
  obtain ⟨envelopeContinuous, driverContinuous, remainingContinuous, envelopeI, driverI, remainingI, initial, history⟩ := drivenData
  let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
    ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let incoming := fun (source : Fin count) time =>
    incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
      (1 + (changed.location (source.val + 1))⁻¹) * magnitude source *
        Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))
  let later := fun (source : Fin count) time =>
    outgoingConstant * changed.circulation (source.val + 1) *
      (changed.circulation (source.val + 1) * (time - entry source) +
        (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
          ‖centroidAsymmetry motion (entry source) source‖)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have gammaNonnegative (source : Fin count) : 0 ≤ changed.circulation (source.val + 1) :=
    (changed.circulation_pos frequencyPositive ratioPositive _).le
  have sourcePointwiseBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      remaining time ≤ sourceEnvelope time + tolerance * prepared.coarserFollowerEnvelope drive time := by
    let completed := Finset.univ.filter (fun source : Fin count => entry source < time)
    have actual := mixed count phase dipoleAngle (prepared.enlargeCap capSource) path time
      ⟨inside.1, inside.2.trans finishBound⟩ drive completed entry initialDistance direction
      (fun source done below => by
        have prior := (Finset.mem_filter.mp done).2
        rcases entries source below with ⟨nonnegative, _, large, tiny, unit, first, second, projection, upper⟩
        exact ⟨nonnegative, prior.le, large, tiny, unit, first, second, projection, upper⟩)
      (fun source below notDone => extents source below time ⟨inside.1, le_of_not_gt (by
        simpa only [completed, Finset.mem_filter, Finset.mem_univ, true_and] using notDone)⟩)
    simp only [remainingInvariant, envelopeInvariant, rawInvariant] at actual
    dsimp only [CascadeSourcePreparedPair.enlargeCap] at actual
    have finiteBound : outgoingBase * (∑ source ∈ finer.filter (fun source => source ∈ completed),
        changed.circulation (source.val + 1) * (4 * ‖centroidAsymmetry motion time source‖ +
          changed.length (source.val + 1) * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
            changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)) +
        incomingConstant * extent ^ 2 * (∑ source ∈ finer.filter (fun source => source ∉ completed),
          changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
            (1 + (changed.location (source.val + 1))⁻¹) * sharpState source time) ≤ sourceEnvelope time := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_ite]
      apply Finset.sum_le_sum
      intro source member
      have below := (Finset.mem_filter.mp member).2
      by_cases done : source ∈ completed
      · have prior := (Finset.mem_filter.mp done).2
        rcases entries source below with ⟨nonnegative, entryBound, large, tiny, unit, first, second, projection, upper⟩
        have actualEnvelope := outgoing count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path source
          (entry source) (path.stop - entry source) (initialDistance source) nonnegative (sub_nonneg.mpr entryBound)
          (by linarith) large tiny (direction source) unit first second projection upper
        have elapsed : time - entry source ∈ Icc 0 (path.stop - entry source) :=
          ⟨(sub_pos.mpr prior).le, sub_le_sub_right (inside.2.trans finishBound) _⟩
        have affine := actualEnvelope.2 (time - entry source) elapsed
        simp only [show entry source + (time - entry source) = time by ring] at affine
        have initialNonnegative : 0 ≤ initialDistance source := by linarith only [large]
        have extra : changed.length (source.val + 1) ^ 2 ≤
            (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
              ‖centroidAsymmetry motion (entry source) source‖ := by
          nlinarith only [mul_nonneg initialNonnegative (sq_nonneg (changed.length (source.val + 1))),
            norm_nonneg (centroidAsymmetry motion (entry source) source)]
        have delayNonnegative := mul_nonneg (gammaNonnegative source) (sub_nonneg.mpr prior.le)
        have scalar : 4 * ‖centroidAsymmetry motion time source‖ + changed.length (source.val + 1) *
            ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ + changed.radius (source.val + 1) ^ 2 +
              changed.length (source.val + 1) ^ 2 ≤
            200000 * (changed.circulation (source.val + 1) * (time - entry source) +
              (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
                ‖centroidAsymmetry motion (entry source) source‖) := by
          nlinarith only [affine, extra, delayNonnegative, sq_nonneg (changed.length (source.val + 1))]
        have scaled := mul_le_mul_of_nonneg_left scalar (mul_nonneg outgoingBaseNonnegative (gammaNonnegative source))
        simp only [done, ite_true, not_le.mpr prior, ite_false]
        convert scaled using 1 <;> dsimp only [later, outgoingConstant] <;> ring
      · have laterEntry : time ≤ entry source := le_of_not_gt (by
          simpa only [completed, Finset.mem_filter, Finset.mem_univ, true_and] using done)
        have scaled := mul_le_mul_of_nonneg_left ((profiles source below).2 time ⟨inside.1, laterEntry⟩)
          (show 0 ≤ incomingConstant * extent ^ 2 * (changed.circulation (source.val + 1) *
            changed.length (source.val + 1) ^ 2 * (1 + (changed.location (source.val + 1))⁻¹)) by
            have locationPositive := changed.location_pos (source.val + 1)
            have gamma := gammaNonnegative source
            positivity)
        simp only [done, ite_false, laterEntry, ite_true]
        convert scaled using 1 <;> dsimp only [incoming, sharpState] <;> ring
    exact actual.trans (add_le_add_right finiteBound _)
  have sourceNonnegative (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ sourceEnvelope time := by
    apply Finset.sum_nonneg
    intro source member
    have below := (Finset.mem_filter.mp member).2
    have gamma := gammaNonnegative source
    have locationPositive := changed.location_pos (source.val + 1)
    have magnitudeNonnegative := (profiles source below).1
    have initialNonnegative : 0 ≤ initialDistance source := by linarith only [(entries source below).2.2.1]
    split_ifs with notYet
    · positivity
    · have delayNonnegative : 0 ≤ time - entry source := sub_nonneg.mpr (le_of_lt (lt_of_not_ge notYet))
      dsimp only [later, outgoingConstant]; positivity
  have sourceI : IntervalIntegrable sourceEnvelope volume 0 finish := by
    have single (source : Fin count) : IntervalIntegrable
        (fun time => if time ≤ entry source then incoming source time else later source time) volume 0 finish := by
      have incomingContinuous : Continuous (incoming source) := by dsimp only [incoming]; fun_prop
      have laterContinuous : Continuous (later source) := by dsimp only [later, outgoingConstant]; fun_prop
      have piecewiseI : Integrable ((Iic (entry source)).piecewise (incoming source) (later source))
          (volume.restrict (uIoc 0 finish)) := Integrable.piecewise measurableSet_Iic
        (incomingContinuous.intervalIntegrable (μ := volume) 0 finish).def'.integrable.integrableOn
        (laterContinuous.intervalIntegrable (μ := volume) 0 finish).def'.integrable.integrableOn
      apply intervalIntegrable_iff.mpr
      simpa only [Set.piecewise, mem_Iic] using piecewiseI
    have finite := IntervalIntegrable.sum (s := finer)
      (f := fun source time => if time ≤ entry source then incoming source time else later source time)
      (fun source _ => single source)
    convert finite using 1
    funext time
    simp only [sourceEnvelope, Finset.sum_apply, incoming, later]
  have macroDominance (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.coarserFollowerEnvelope drive time ≤ geometryConstant * envelope time := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg geometryNonnegative (norm_nonneg _))).mpr
    intro receiver
    by_cases below : receiver.val < drive.val
    · have receiverNonterminal : receiver.val + 1 < count := by omega
      obtain ⟨chosen, properties, polar, _, _, _, bounds⟩ := geometryEstimate prepared path receiver receiverNonterminal finish
        finishNonnegative finishBound (fun time inside => (small receiver below time inside).trans (min_le_right _ _))
      have equality := (coherence prepared path receiver finish finishNonnegative finishBound
        (fun time inside => (small receiver below time inside).trans ((min_le_left _ _).trans drivenQuarter)) chosen (lift receiver)
        (fun side => (properties side).1.continuousOn) (fun side => (liftProperties receiver side).1.continuousOn)
        (fun side => (properties side).2.trans (liftProperties receiver side).2.symm) polar (liftPolar receiver below)).2.2 graph coordinate
      have bound := (bounds time inside).2
      rw [equality inside] at bound
      have stateNonnegative : 0 ≤ prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
          ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch := by
        have locationPositive := changed.location_pos (receiver.val + 1)
        dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize, CascadeSourcePreparedPair.rawSourceShapeBudget]
        positivity
      have enlarged := bound.trans (mul_le_mul_of_nonneg_right (le_max_right drivenGeometry freshGeometry) stateNonnegative)
      have scaled := mul_le_mul_of_nonneg_left enlarged (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
      have component := norm_le_pi_norm (fun current : Fin count => if current.val < drive.val then
        changed.location (current.val + 1) ^ 4 * (prepared.finiteCoordinateSize graph coordinate (lift current) current time +
          ∑ patch : Fin 4, prepared.rawSourceShapeBudget time current patch) else 0) receiver
      have stateScaled : 0 ≤ changed.location (receiver.val + 1) ^ 4 *
          (prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) := mul_nonneg (by positivity) stateNonnegative
      simp only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg stateScaled] at component
      have bounded := (show prepared.weightedMacroSourceState time receiver ≤ geometryConstant *
          (changed.location (receiver.val + 1) ^ 4 * (prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch)) by
        convert scaled using 1; dsimp only [CascadeSourcePreparedPair.weightedMacroSourceState]; ring).trans
        (mul_le_mul_of_nonneg_left component geometryNonnegative)
      have macroNonnegative : 0 ≤ prepared.weightedMacroSourceState time receiver :=
        mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time receiver)
      simpa only [CascadeSourcePreparedPair.coarserFollowerEnvelope, below, ite_true, Real.norm_eq_abs, abs_of_nonneg macroNonnegative] using bounded
    · simp only [below, ite_false, norm_zero]
      exact mul_nonneg geometryNonnegative (norm_nonneg _)
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) :
      0 ≤ sourceEnvelope time ∧ remaining time ≤ sourceEnvelope time + tolerance * (geometryConstant * envelope time) := by
    exact ⟨sourceNonnegative time inside, (sourcePointwiseBound time inside).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left (macroDominance time inside) tolerancePositive.le) _)⟩
  have rhoNonnegative : 0 ≤ rho := by
    have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]; positivity
  let originalForcing := fun time => rowConstant * rho * (geometryConstant * envelope time + driver time) + remaining time
  let adjusted := fun time => rowConstant * rho * driver time + remaining time - tolerance * geometryConstant * envelope time
  have originalContinuous : ContinuousOn originalForcing (Icc 0 finish) :=
    (continuousOn_const.mul ((continuousOn_const.mul envelopeContinuous).add driverContinuous)).add remainingContinuous
  have adjustedContinuous : ContinuousOn adjusted (Icc 0 finish) :=
    ((continuousOn_const.mul driverContinuous).add remainingContinuous).sub (continuousOn_const.mul envelopeContinuous)
  have preliminary (time : ℝ) (inside : time ∈ Icc 0 finish) :
      envelope time ≤ multiplier * ∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * originalForcing current := by
    have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have kernelContinuous : Continuous (fun current : ℝ => Real.exp (growth * (time - current))) := by fun_prop
    have originalI := (kernelContinuous.continuousOn.mul (originalContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    have comparison := intervalIntegral.integral_mono_on inside.1 (history time inside).1 originalI (by
      intro current member
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have enlarged := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_left drivenGeometry freshGeometry)
          (show 0 ≤ envelope current from norm_nonneg _))
        (mul_nonneg rowNonnegative rhoNonnegative)
      change rowConstant * rho * (drivenGeometry * envelope current + driver current) + remaining current ≤
        originalForcing current
      dsimp only [originalForcing]
      nlinarith only [enlarged])
    exact (history time inside).2.2.1 |>.trans (mul_le_mul_of_nonneg_left comparison multiplierNonnegative)
  have feedbackNonnegative : 0 ≤ feedback := by dsimp only [feedback]; positivity
  have adjustedHistory : ∀ time ∈ Icc 0 finish,
      envelope time ≤ (0 : ℝ) * Real.exp (growth * time) + multiplier * ∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * (adjusted current + feedback * envelope current) := by
    intro time inside
    have identity : originalForcing = fun current => adjusted current + feedback * envelope current := by
      funext current; dsimp only [originalForcing, adjusted, feedback]; ring
    have actual := preliminary time inside
    rw [identity] at actual
    simpa only [zero_mul, zero_add] using actual
  have resolved := EulerNonuniqueness.exponential_volterra_gronwall envelopeContinuous adjustedContinuous feedbackNonnegative
    multiplierNonnegative finishNonnegative adjustedHistory
  refine ⟨lift, liftProperties, liftPolar, envelopeContinuous, driverContinuous, remainingContinuous,
    envelopeI, driverI, remainingI, initial, macroDominance, pointwise, sourceI, ?_⟩
  intro time inside
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have integralSubset : uIcc (0 : ℝ) time ⊆ uIcc 0 finish := by
    rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]
    exact prefixSubset
  have kernelContinuous : Continuous (fun current : ℝ => Real.exp ((growth + multiplier * feedback) * (time - current))) := by fun_prop
  have sourceKernelI := (sourceI.mono_set integralSubset).mul_continuousOn kernelContinuous.continuousOn
  have driverKernelI : IntervalIntegrable (fun current => Real.exp ((growth + multiplier * feedback) * (time - current)) *
      (rowConstant * rho * driver current)) volume 0 time :=
    (kernelContinuous.continuousOn.mul (continuousOn_const.mul (driverContinuous.mono prefixSubset))).intervalIntegrable_of_Icc (μ := volume) inside.1
  have majorantI : IntervalIntegrable (fun current => Real.exp ((growth + multiplier * feedback) * (time - current)) *
      (rowConstant * rho * driver current + sourceEnvelope current)) volume 0 time := by
    convert driverKernelI.add sourceKernelI using 1
    funext current; ring
  have adjustedI := (kernelContinuous.continuousOn.mul (adjustedContinuous.mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have comparison := intervalIntegral.integral_mono_on inside.1 adjustedI majorantI (by
    intro current member
    have bound := (pointwise current (prefixSubset member)).2
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    dsimp only [adjusted]
    nlinarith only [bound])
  refine ⟨majorantI, ?_⟩
  have actual := resolved time inside
  simp only [zero_mul, zero_add] at actual
  exact actual.trans (mul_le_mul_of_nonneg_left comparison multiplierNonnegative)

end EulerNonuniqueness.Paper
