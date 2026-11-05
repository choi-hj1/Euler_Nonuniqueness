import EulerNonuniqueness.Section5.CascadeMixedForeignPatchOriginalPrefixBudget
import EulerNonuniqueness.Section5.CascadeMixedFollowerClosedPrefixBudget
import EulerNonuniqueness.Section5.CascadeFollowerEnvelopeArbitraryWeightReturn
import EulerNonuniqueness.Section5.CascadePhaseLiftCoherence
import EulerNonuniqueness.General.FinitePrefixMask

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem mixed_patch_closed_scalar
    {own mask envelope driver remaining macroValue sharp common coarse responseE responseK rho tolerance distance weight : ℝ}
    (distancePositive : 0 < distance) (weightPositive : 0 < weight)
    (coarseNonnegative : 0 ≤ coarse) (responseNonnegative : 0 ≤ responseE) (rhoNonnegative : 0 ≤ rho)
    (ownBound : own ≤ coarse / distance ^ 4 * rho * mask + sharp + tolerance * macroValue)
    (maskBound : mask ≤ envelope + driver)
    (envelopeBound : envelope ≤ (2 * responseE / weight) * (rho * driver + remaining))
    (remainingBound : remaining ≤ 2 * common + (4 * responseK / weight) * driver)
    (driverIdentity : driver = distance ^ 4 * macroValue) :
    own ≤ sharp + (4 * coarse * responseE * rho / (weight * distance ^ 4)) * common +
      (coarse * rho * (1 + 2 * responseE * rho / weight + 8 * responseE * responseK / weight ^ 2) + tolerance) * macroValue := by
  have responseNonnegative' : 0 ≤ 2 * responseE / weight := div_nonneg (by positivity) weightPositive.le
  have envelopeClosed : envelope ≤ (2 * responseE / weight) *
      (rho * driver + (2 * common + (4 * responseK / weight) * driver)) :=
    envelopeBound.trans (mul_le_mul_of_nonneg_left (add_le_add_left remainingBound _) responseNonnegative')
  have maskClosed := maskBound.trans (add_le_add_right envelopeClosed driver)
  have scaled := mul_le_mul_of_nonneg_left maskClosed
    (mul_nonneg (div_nonneg coarseNonnegative (pow_nonneg distancePositive.le 4)) rhoNonnegative)
  have result := ownBound.trans (add_le_add_right (add_le_add_right scaled sharp) (tolerance * macroValue))
  rw [driverIdentity] at result
  convert result using 1
  field_simp [distancePositive.ne', weightPositive.ne']
  ring

theorem exists_uniform_actual_mixed_foreign_patch_closed_weighted_budget
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ coarseConstant ≥ (0 : ℝ), ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∃ commonIncoming ≥ (0 : ℝ), ∃ commonOutgoing ≥ (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseE ≥ (1 : ℝ), ∃ responseK ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ accuracy : ℝ, 0 < accuracy →
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (max (2 * responseE) (4 * responseK)) ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant : ℝ), 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ receiver : Fin count, receiver.val + 1 < count →
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
    ∀ finish ∈ Icc 0 terminal,
    (∀ current : Fin count, current.val ≤ receiver.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time current| + |stableShape motion time current| ≤ radius) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
    (∀ side, suppliedLift side 0 = phase (receiver.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
          Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
    ∀ weight : ℝ, 2 * changed.omega (receiver.val + 1) ≤ weight →
    (∀ source : Fin count, receiver.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let ownForcing := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid motion current receiver patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) ownRadius (power + 1) time‖
    let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
    let finer := Finset.univ.filter (fun source : Fin count => receiver.val < source.val)
    let commonBudget := commonIncoming * extent ^ 2 * (∑ source ∈ finer,
      changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
        (1 + (changed.location (source.val + 1))⁻¹) * magnitude source /
        (coefficient * changed.omega (source.val + 1)) * Real.exp (-weight * entry source)) +
      commonOutgoing * (∑ source ∈ finer.filter (fun source => entry source < finish),
        changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) / weight ^ 2 +
          ((1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
            ‖centroidAsymmetry motion (entry source) source‖) / weight) * Real.exp (-weight * entry source))
    ContinuousOn ownForcing (Icc 0 path.stop) ∧ ContinuousOn stateBudget (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * ownForcing time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * stateBudget time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ownForcing time) ≤
      prepared.mixedSelectedFinerSourcePrefixBudget receiver incomingConstant outgoingConstant extent coefficient
        entry initialDistance magnitude weight finish +
      (4 * coarseConstant * responseE * (216360000 * changed.hessian + 576 * changed.strain) /
        (weight * changed.location (receiver.val + 1) ^ 4)) * commonBudget +
      accuracy * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * stateBudget time) := by
  classical
  obtain ⟨patchThreshold, patchThresholdPositive, patchThresholdEighth, patchCap, patchCapPositive,
    coarseConstant, coarseNonnegative, patchIncoming, patchIncomingNonnegative, patchOutgoing, patchOutgoingNonnegative, patches⟩ :=
    exists_uniform_actual_mixed_foreign_patch_original_prefix_budget
  obtain ⟨envelopeThreshold, envelopeThresholdPositive, _, envelopeCap, envelopeCapPositive, envelopes⟩ :=
    exists_uniform_actual_follower_envelope_arbitrary_weight_return
  obtain ⟨remainingThreshold, remainingThresholdPositive, _, remainingCap, remainingCapPositive,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative, remainings⟩ :=
    exists_uniform_actual_mixed_follower_closed_prefix_budget
  obtain ⟨geometryRadius, geometryPositive, geometryQuarter, geometryConstant, geometryOne, geometry⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨stateCap, stateCapPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min patchCap (min envelopeCap (min remainingCap stateCap))
  let thresholdMax := min patchThreshold (min envelopeThreshold remainingThreshold)
  have capPositive : 0 < rawCap := lt_min patchCapPositive (lt_min envelopeCapPositive (lt_min remainingCapPositive stateCapPositive))
  have patchCapBound : rawCap ≤ patchCap := min_le_left _ _
  have envelopeCapBound : rawCap ≤ envelopeCap := (min_le_right _ _).trans (min_le_left _ _)
  have remainingCapBound : rawCap ≤ remainingCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have stateCapBound : rawCap ≤ stateCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨thresholdMax, lt_min patchThresholdPositive (lt_min envelopeThresholdPositive remainingThresholdPositive),
    (min_le_left _ _).trans patchThresholdEighth, rawCap, capPositive, coarseConstant, coarseNonnegative,
    patchIncoming, patchIncomingNonnegative, patchOutgoing, patchOutgoingNonnegative,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨envelopeRadius, envelopePositive, _, responseE, responseEOne, rootE, rootEEight, envelopeFactory⟩ := envelopes factorPositive factorSmall
  obtain ⟨remainingRadius, remainingPositive, _, responseK, responseKOne, rootK, rootKEight, remainingFactory⟩ := remainings factorPositive factorSmall
  let radius := min geometryRadius (min envelopeRadius remainingRadius)
  let rootMin := max rootE rootK
  have radiusGeometry : radius ≤ geometryRadius := min_le_left _ _
  have radiusEnvelope : radius ≤ envelopeRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusRemaining : radius ≤ remainingRadius := (min_le_right _ _).trans (min_le_right _ _)
  have radiusQuarter : radius ≤ 1 / 4 := radiusGeometry.trans geometryQuarter
  refine ⟨radius, lt_min geometryPositive (lt_min envelopePositive remainingPositive), radiusQuarter,
    responseE, responseEOne, responseK, responseKOne, rootMin, rootEEight.trans (le_max_left _ _), ?_⟩
  intro extent extentOne accuracy accuracyPositive scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant boundaryOne
  have rootELarge : rootE ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have rootKLarge : rootK ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEEight.trans rootELarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioE : max 2 (2 * responseE) ≤ scales.ratio := max_le ratioBound
    ((le_max_left _ _).trans ((le_max_right _ _).trans ratioLarge))
  have ratioK : max 2 (4 * responseK) ≤ scales.ratio := max_le ratioBound
    ((le_max_right _ _).trans ((le_max_right _ _).trans ratioLarge))
  have geometryPositive' : 0 < geometryConstant := zero_lt_one.trans_le geometryOne
  let tolerance := accuracy / (4 * geometryConstant)
  have tolerancePositive : 0 < tolerance := by dsimp only [tolerance]; positivity
  let rhoAt := fun frequency : ℝ => 216360000 * ({scales with frequency := frequency} : Scales).hessian +
    576 * ({scales with frequency := frequency} : Scales).strain
  have rhoDecay : Tendsto rhoAt atTop (𝓝 0) := by
    simpa only [rhoAt, mul_zero, zero_add] using
      (((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576))
  have coefficientDecay : Tendsto (fun frequency => coarseConstant * rhoAt frequency *
      (1 + 2 * responseE * rhoAt frequency + 8 * responseE * responseK) * geometryConstant) atTop (𝓝 0) := by
    have regular : Continuous (fun value : ℝ => coarseConstant * value *
      (1 + 2 * responseE * value + 8 * responseE * responseK) * geometryConstant) := by fun_prop
    simpa only [mul_zero, zero_mul] using (regular.tendsto 0).comp rhoDecay
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  filter_upwards [patches extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans (min_le_left _ _))
      orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    envelopeFactory scales scaleRoot rootELarge amplitudeIdentity ratioE alphaPositive threshold referenceConstant boundaryConstant
      (thresholdBound.trans ((min_le_right _ _).trans (min_le_left _ _))) referenceNonnegative boundaryOne orbit sectionTime,
    remainingFactory scales scaleRoot rootKLarge amplitudeIdentity ratioK alphaPositive extent extentOne referenceConstant referenceNonnegative
      referenceAmplitude threshold (thresholdBound.trans ((min_le_right _ _).trans (min_le_right _ _))) orbit sectionTime boundaryConstant boundaryOne,
    geometry scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne)
      factorPositive factorEighth (thresholdBound.trans ((min_le_left _ _).trans patchThresholdEighth)) referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    coefficientDecay.eventually (eventually_lt_nhds (half_pos accuracyPositive)), eventually_ge_atTop (1 : ℝ)]
    with frequency patchEstimate envelopeEstimate remainingEstimate geometryEstimate coherence coefficientSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal terminal terminalNonnegative terminalBound entry initialDistance direction
  dsimp only
  intro entries extents coefficient coefficientPositive magnitude profiles finish finishInside small suppliedLift suppliedContinuous suppliedInitial suppliedPolar weight weightLower rateBounds
  let changed : Scales := {scales with frequency := frequency}
  let location := changed.location (receiver.val + 1)
  let rho := rhoAt frequency
  let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
  let own := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current receiver patch) ownRadius (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) ownRadius (power + 1) time‖
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
  let state := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time + raw time
  let macroValue := fun time => prepared.macroSourceState time receiver
  let mask := fun time => ‖fun source : Fin count => if source.val ≤ receiver.val then changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖
  let envelope := prepared.coarserFollowerEnvelope receiver
  let remaining := prepared.followerStrictlyFinerForcing receiver
  let driver := fun time => prepared.weightedMacroSourceState time receiver
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  let patchBudget := prepared.mixedSelectedFinerSourcePrefixBudget receiver patchIncoming patchOutgoing extent coefficient entry initialDistance magnitude weight finish
  let finer := Finset.univ.filter (fun source : Fin count => receiver.val < source.val)
  let commonBudget := commonIncoming * extent ^ 2 * (∑ source ∈ finer,
    changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
      (1 + (changed.location (source.val + 1))⁻¹) * magnitude source /
      (coefficient * changed.omega (source.val + 1)) * Real.exp (-weight * entry source)) +
    commonOutgoing * (∑ source ∈ finer.filter (fun source => entry source < finish),
      changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) / weight ^ 2 +
        ((1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
          ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion (entry source) source‖) / weight) * Real.exp (-weight * entry source))
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaOne : 1 ≤ changed.omega (receiver.val + 1) := frequencyOne.trans
    (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have omegaWeight : changed.omega (receiver.val + 1) ≤ weight :=
    (le_mul_of_one_le_left (zero_le_one.trans omegaOne) (by norm_num : (1 : ℝ) ≤ 2)).trans weightLower
  have weightOne : 1 ≤ weight := omegaOne.trans omegaWeight
  have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
  have locationPositive : 0 < location := changed.location_pos _
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source => div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source => div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    exact add_nonneg (mul_nonneg (by norm_num) hessianNonnegative) (mul_nonneg (by norm_num) strainNonnegative)
  have macroInvariant {larger : ℝ} (bound : rawCap ≤ larger) : (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source; with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have centerInvariant {larger : ℝ} (bound : rawCap ≤ larger) : (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source; with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawInvariant {larger : ℝ} (bound : rawCap ≤ larger) : (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch; with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have driverInvariant {larger : ℝ} (bound : rawCap ≤ larger) : (prepared.enlargeCap bound).weightedMacroSourceState = prepared.weightedMacroSourceState := by
    funext time source; simp only [CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have envelopeInvariant {larger : ℝ} (bound : rawCap ≤ larger) : (prepared.enlargeCap bound).coarserFollowerEnvelope = prepared.coarserFollowerEnvelope := by
    funext index time; simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, driverInvariant]
  have remainingInvariant {larger : ℝ} (bound : rawCap ≤ larger) : (prepared.enlargeCap bound).followerStrictlyFinerForcing = prepared.followerStrictlyFinerForcing := by
    funext index time
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.followerStrictlyFinerForcing,
      CascadeSourcePreparedPair.selectedForeignForcing, CascadeSourcePreparedPair.coarserBlockCoefficientTerm,
      CascadeSourcePreparedPair.coarserPatchCoefficientTerm]
  have budgetInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).mixedSelectedFinerSourcePrefixBudget = prepared.mixedSelectedFinerSourcePrefixBudget := by
    funext index incoming outgoing extent coefficient entry initialDistance magnitude weight finish
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.mixedSelectedFinerSourcePrefixBudget]
  have patchData := patchEstimate count phase dipoleAngle (prepared.enlargeCap patchCapBound) path receiver terminal terminalNonnegative terminalBound
    entry initialDistance direction entries extents coefficient coefficientPositive magnitude (by simpa only [centerInvariant, rawInvariant] using profiles)
    finish finishInside weight weightPositive rateBounds
  dsimp only at patchData
  simp only [macroInvariant, budgetInvariant] at patchData
  with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at patchData
  obtain ⟨ownContinuous, maskContinuous, macroContinuous, ownI, maskI, macroI, ownBound⟩ := patchData
  have envelopeData := envelopeEstimate count phase dipoleAngle (prepared.enlargeCap envelopeCapBound) path receiver nonterminal finish finishInside.1
    (finishInside.2.trans terminalBound) (fun current below time inside => (small current below.le time inside).trans radiusEnvelope) weight weightLower
  dsimp only at envelopeData
  simp only [envelopeInvariant, driverInvariant, remainingInvariant] at envelopeData
  obtain ⟨_, driverContinuous, _, _, _, _, envelopeI, driverI, remainingI, envelopeBound⟩ := envelopeData
  have remainingData := remainingEstimate count phase dipoleAngle (prepared.enlargeCap remainingCapBound) path receiver nonterminal terminal terminalNonnegative terminalBound
    entry initialDistance direction entries extents coefficient coefficientPositive magnitude (by simpa only [centerInvariant, rawInvariant] using profiles)
    finish finishInside (fun current below time inside => (small current below.le time inside).trans radiusRemaining) weight omegaWeight rateBounds
  dsimp only at remainingData
  simp only [envelopeInvariant, driverInvariant, remainingInvariant, rawInvariant, centerInvariant] at remainingData
  with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at remainingData
  obtain ⟨_, _, _, _, _, _, _, _, _, remainingBound⟩ := remainingData
  obtain ⟨lift, liftContinuous, liftPolar, coordinateContinuous, _, coordinateNonnegative, geometryBounds⟩ :=
    geometryEstimate prepared path receiver nonterminal finish finishInside.1 (finishInside.2.trans terminalBound)
      (fun time inside => (small receiver le_rfl time inside).trans radiusGeometry)
  have liftEquality := (coherence prepared path receiver finish finishInside.1 (finishInside.2.trans terminalBound)
    (fun time inside => (small receiver le_rfl time inside).trans radiusQuarter) lift suppliedLift
    (fun side => (liftContinuous side).1.continuousOn) suppliedContinuous
    (fun side => (liftContinuous side).2.trans (suppliedInitial side).symm) liftPolar suppliedPolar).2.2 graph coordinate
  have coordinateContinuous' := coordinateContinuous.congr (fun time inside => (liftEquality inside).symm)
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum Finset.univ
    (fun patch _ => ((stateContinuity prepared capPositive stateCapBound path receiver).1 patch).mono
      (Icc_subset_Icc le_rfl (finishInside.2.trans terminalBound)))
  have stateContinuous : ContinuousOn state (Icc 0 finish) := coordinateContinuous'.add rawContinuous
  have exponential : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have stateI := (exponential.continuousOn.mul stateContinuous).intervalIntegrable_of_Icc (μ := volume) finishInside.1
  have macroActionBound : weighted macroValue ≤ geometryConstant * weighted state := by
    have comparison := intervalIntegral.integral_mono_on finishInside.1 macroI (stateI.const_mul geometryConstant) (by
      intro time inside
      have actual := (geometryBounds time inside).2
      rw [liftEquality inside] at actual
      have scaled := mul_le_mul_of_nonneg_left actual (Real.exp_pos (-weight * time)).le
      convert scaled using 1; ring)
    simpa only [intervalIntegral.integral_const_mul] using comparison
  have maskActionBound : weighted mask ≤ weighted envelope + weighted driver := by
    have comparison := intervalIntegral.integral_mono_on finishInside.1 maskI (envelopeI.add driverI) (by
      intro time inside
      have actual := General.norm_prefix_with_receiver_nonnegative_le
        (fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source)
        (fun source => mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time source)) receiver receiver le_rfl
      have actual' : mask time ≤ envelope time + driver time := by
        simpa only [← le_iff_lt_or_eq, ite_true, CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState] using actual
      have scaled := mul_le_mul_of_nonneg_left actual' (Real.exp_pos (-weight * time)).le
      convert scaled using 1; ring)
    simpa only [intervalIntegral.integral_add envelopeI driverI] using comparison
  have driverIdentity : weighted driver = location ^ 4 * weighted macroValue := by
    change (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (location ^ 4 * macroValue time)) =
      location ^ 4 * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * macroValue time)
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    ring
  change weighted own ≤ coarseConstant / location ^ 4 * rho * weighted mask + patchBudget + tolerance * weighted macroValue at ownBound
  change weighted envelope ≤ (2 * responseE / weight) * (rho * weighted driver + weighted remaining) at envelopeBound
  change weighted remaining ≤ 2 * commonBudget + (4 * responseK / weight) * weighted driver at remainingBound
  have closed := mixed_patch_closed_scalar locationPositive weightPositive coarseNonnegative (zero_le_one.trans responseEOne) rhoNonnegative
    ownBound maskActionBound envelopeBound remainingBound driverIdentity
  let feedback := coarseConstant * rho * (1 + 2 * responseE * rho / weight + 8 * responseE * responseK / weight ^ 2) + tolerance
  have numeratorOne : 0 ≤ 2 * responseE * rho := by positivity
  have numeratorTwo : 0 ≤ 8 * responseE * responseK := by positivity
  have quotientOne : 2 * responseE * rho / weight ≤ 2 * responseE * rho :=
    (div_le_iff₀ weightPositive).mpr (le_mul_of_one_le_right numeratorOne weightOne)
  have quotientTwo : 8 * responseE * responseK / weight ^ 2 ≤ 8 * responseE * responseK :=
    (div_le_iff₀ (sq_pos_of_pos weightPositive)).mpr (le_mul_of_one_le_right numeratorTwo (one_le_pow₀ weightOne))
  have feedbackBound : feedback ≤ coarseConstant * rho * (1 + 2 * responseE * rho + 8 * responseE * responseK) + tolerance :=
    add_le_add_right (mul_le_mul_of_nonneg_left (by linarith only [quotientOne, quotientTwo]) (mul_nonneg coarseNonnegative rhoNonnegative)) tolerance
  have toleranceIdentity : tolerance * geometryConstant = accuracy / 4 := by dsimp only [tolerance]; field_simp [geometryPositive'.ne']; ring
  have feedbackSmall : feedback * geometryConstant ≤ accuracy := by
    have actualSmall : coarseConstant * rho * (1 + 2 * responseE * rho + 8 * responseE * responseK) * geometryConstant < accuracy / 2 := coefficientSmall
    calc
      _ ≤ (coarseConstant * rho * (1 + 2 * responseE * rho + 8 * responseE * responseK) + tolerance) * geometryConstant :=
        mul_le_mul_of_nonneg_right feedbackBound geometryPositive'.le
      _ = coarseConstant * rho * (1 + 2 * responseE * rho + 8 * responseE * responseK) * geometryConstant + accuracy / 4 := by rw [add_mul, toleranceIdentity]
      _ ≤ accuracy := by linarith only [actualSmall, accuracyPositive]
  have feedbackNonnegative : 0 ≤ feedback := by dsimp only [feedback]; positivity
  have stateNonnegative (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ state time := by
    have actual : 0 ≤ prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time := by rw [← liftEquality inside]; exact coordinateNonnegative time
    have rawNonnegative : 0 ≤ raw time := by dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
    exact add_nonneg actual rawNonnegative
  have stateActionNonnegative : 0 ≤ weighted state := intervalIntegral.integral_nonneg finishInside.1
    (fun time inside => mul_nonneg (Real.exp_pos _).le (stateNonnegative time inside))
  have replaced := (mul_le_mul_of_nonneg_left macroActionBound feedbackNonnegative).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right feedbackSmall stateActionNonnegative)
  refine ⟨ownContinuous, stateContinuous, ownI, stateI, ?_⟩
  change weighted own ≤ patchBudget + (4 * coarseConstant * responseE * rho / (weight * location ^ 4)) * commonBudget + accuracy * weighted state
  exact closed.trans (add_le_add_left replaced _)

end EulerNonuniqueness.Paper

