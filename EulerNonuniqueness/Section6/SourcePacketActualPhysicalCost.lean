import EulerNonuniqueness.Section6.SourcePacketActualSourceCost

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000

theorem exists_source_packet_actual_reference_frame_physical_cost :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant receiverRadiusFactor radiusFactor constant chartRadius tolerance initialError : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant → 0 < receiverRadiusFactor →
    0 < radiusFactor → 0 ≤ constant → 0 < chartRadius → 0 < tolerance → initialError ≤ 1 / 64 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val + 1 = source.val → ∀ patch : Fin 4,
    ∀ start horizon initialDistance outgoingPhase : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    2048 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    12 * initialDistance ≤ scales.ratio →
    20 * initialError + 83200 / initialDistance ^ 2 ≤ min tolerance 1 / 5120 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ initialError * length →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ initialError * length →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    (∀ time ∈ Icc 0 start, ∀ label, motion.domain time source label ⊆
      closedBall (quadrupoleCenter motion time source) (radiusFactor * length)) →
    (∀ elapsed ∈ Icc 0 horizon, ‖patchCentroid motion (start + elapsed) receiver patch -
      quadrupoleCenter motion (start + elapsed) receiver‖ ≤ receiverRadiusFactor * changed.length (receiver.val + 1)) →
    ∃ geometry : SourcePacketPhysicalGeometry prepared.trajectory.movingFamily changed source start horizon chartRadius,
      SourcePacketMaterialNormalization geometry prepared.referenceWitness.trajectory.movingFamily.patchMotion receiver patch
        (fun index => phase (index.val + 1)) outgoingPhase
        (boundaryConstant / (scaleRoot ^ 2 * changed.omega (source.val + 1) ^ 2)) ∧
      IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
        geometry.physicalCost constant elapsed) volume 0 horizon ∧
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
        geometry.physicalCost constant elapsed) ≤
        tolerance * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 *
            ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ ^ 4)) := by
  obtain ⟨geometryRadius, geometryRadiusPositive, geometryRadiusSmall, material⟩ := exists_source_packet_material_reference_frame_geometry
  obtain ⟨phaseRadius, phaseRadiusPositive, phaseRadiusSmall, phaseCost⟩ := exists_source_packet_reference_frame_phase_cost
  obtain ⟨recipientRadius, recipientRadiusPositive, recipientRadiusSmall, recipient⟩ := exists_source_packet_reference_recipient
  let radius := min geometryRadius (min phaseRadius recipientRadius)
  refine ⟨radius, by dsimp only [radius]; positivity, (min_le_left _ _).trans geometryRadiusSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant receiverRadiusFactor radiusFactor constant chartRadius tolerance initialError
    factorPositive factorSmall rootOne boundaryOne receiverRadiusPositive radiusFactorPositive constantNonnegative chartRadiusPositive
    tolerancePositive initialErrorSmall
  let budget := min tolerance 1
  let chartBound := budget / (16 * (constant + 1))
  have budgetPositive : 0 < budget := lt_min tolerancePositive (by norm_num)
  have budgetOne : budget ≤ 1 := min_le_right _ _
  have budgetTolerance : budget ≤ tolerance := min_le_left _ _
  have chartBoundPositive : 0 < chartBound := by dsimp only [chartBound]; positivity
  have factorOne : factor ≤ 1 := by linarith
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  have thresholdSmall : threshold ≤ 1 / 2 :=
    (thresholdBound.trans ((min_le_left _ _).trans geometryRadiusSmall)).trans (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    material scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold
      (thresholdBound.trans (min_le_left _ _)) orbit sectionTime factor scaleRoot boundaryConstant receiverRadiusFactor chartRadius
      factorPositive factorOne rootOne boundaryOne receiverRadiusPositive chartRadiusPositive,
    recipient scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold
      (thresholdBound.trans ((min_le_right _ _).trans (min_le_right _ _))) chartBound 1 chartBoundPositive (by norm_num),
    phaseCost scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold
      (thresholdBound.trans ((min_le_right _ _).trans (min_le_left _ _))) orbit sectionTime factor scaleRoot boundaryConstant
      (budget / 4) factorPositive factorOne rootPositive boundaryNonnegative (by positivity),
    scales.eventually_actual_source_packet_sourceCost amplitudePositive ratioBound alphaPositive orbit sectionTime factorPositive
      factorSmall thresholdSmall rootOne boundaryOne receiverRadiusPositive radiusFactorPositive (tolerance := budget / 4)
      (by positivity) initialErrorSmall,
    scales.eventually_actual_inherited_moment_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne rootPositive boundaryNonnegative (by norm_num : (0 : ℝ) < 1)]
    with frequency frequencyOne material recipient phaseCost sourceCost inherited
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent patch start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prefixBounded receiverRadius
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let length := changed.length (source.val + 1)
  let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
  let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  let seed := Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * ‖frozen‖ ^ 4)
  let decay := 2 * Real.sqrt 2 * changed.omega source.val
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive : 0 < length := changed.length_pos _
  have directionNorm : ‖direction‖ = 1 := by dsimp only [direction]; rw [Complex.norm_exp]; simp
  have different : receiver ≠ source := by intro equality; subst source; omega
  have frozenPositive : 0 < ‖frozen‖ := by
    dsimp only [frozen]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact changed.location_distance_pos (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have firstCoarse : ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 := by
    have bound := mul_le_mul_of_nonneg_right initialErrorSmall lengthPositive.le
    linarith
  have secondCoarse : ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 := by
    have bound := mul_le_mul_of_nonneg_right initialErrorSmall lengthPositive.le
    linarith
  obtain ⟨geometry, normalization⟩ := material count phase dipoleAngle prepared path receiver source different patch start horizon initialDistance
    outgoingPhase startNonnegative horizonNonnegative endBound (by linarith) initialDistanceSmall direction directionNorm firstCoarse secondCoarse
    initialProjection initialUpper receiverRadius
  have sourceBound := sourceCost count phase dipoleAngle prepared path receiver source different patch start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget
    (by convert initialBudget using 1 <;> dsimp only [budget] <;> ring) firstInitial secondInitial initialProjection initialUpper
    prefixBounded receiverRadius geometry normalization
  have phaseBound := phaseCost count phase dipoleAngle prepared path receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound (by linarith) ratioBudget direction frozen directionNorm
    (norm_pos_iff.mp frozenPositive) firstCoarse secondCoarse initialUpper
  have actualPhaseBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.phaseCost elapsed) ≤ (budget / 4) * seed := by
    simp_rw [SourcePacketPhysicalGeometry.phaseCost, SourcePacketPhysicalGeometry.modelStrain, source_packet_model_strain_norm,
      normalization.frozenDisplacement, normalization.targetMoment, normalization.positive, normalization.idealPositive]
    simpa only [adjacent, frozen, decay, seed] using phaseBound.2
  let moment := ∫ position, quadrupoleDensity changed motion start source position •
    (position - quadrupoleCenter motion start source) ^ 2
  have startInside : start ∈ Icc 0 path.stop := ⟨startNonnegative, by linarith⟩
  have inheritedBound := inherited count phase dipoleAngle prepared path source start startInside initialDistance (by linarith)
    (by simpa using ratioBudget) direction frozen directionNorm (norm_pos_iff.mp frozenPositive) firstCoarse secondCoarse initialUpper
  have target := changed.retained_target_moment_weighted_bound source.val frequencyPositive ratioPositive moment outgoingPhase horizon ‖frozen‖ 1
    horizonNonnegative frozenPositive inheritedBound
  have targetBound : (6 / (Real.pi * ‖geometry.frozenDisplacement‖ ^ 4)) *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖geometry.targetMoment elapsed‖) ≤ 4 * seed := by
    simpa only [normalization.frozenDisplacement, normalization.targetMoment, moment, frozen, decay, seed,
      show (1 + 3 : ℝ) = 4 by norm_num] using target
  have chartSmall (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).1| +
        |(pointShapeChart (geometry.positive elapsed) (geometry.negative elapsed)).2| ≤ chartBound := by
    rw [normalization.positive, normalization.negative]
    exact (recipient prepared.referenceWitness (start + elapsed)
      ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩ receiver).2.2.1
  have combined := geometry.weighted_physicalCost_le_literal_budgets horizonNonnegative constantNonnegative chartSmall sourceBound targetBound actualPhaseBound
  have chartConstant : constant * chartBound / 4 ≤ budget / 64 := by
    dsimp only [chartBound]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have ratio : constant / (constant + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have multiplied := mul_le_mul_of_nonneg_left ratio budgetPositive.le
    have identity : constant * (budget / (16 * (constant + 1))) = (budget * (constant / (constant + 1))) / 16 := by
      field_simp [show constant + 1 ≠ 0 by positivity] <;> ring
    rw [identity]
    linarith
  have chartTotal := mul_le_mul chartConstant (show 4 + budget / 4 ≤ (17 / 4 : ℝ) by linarith)
    (show 0 ≤ 4 + budget / 4 by positivity) (show 0 ≤ budget / 64 by positivity)
  have coefficient : (constant * chartBound / 4) * (4 + budget / 4) + budget / 4 + budget / 4 ≤ tolerance := by
    nlinarith
  have seedNonnegative : 0 ≤ seed := by dsimp only [seed]; positivity
  refine ⟨geometry, normalization, geometry.weighted_physicalCost_integrable horizonNonnegative constantNonnegative,
    combined.trans ?_⟩
  exact mul_le_mul_of_nonneg_right coefficient seedNonnegative

end EulerNonuniqueness.Paper
