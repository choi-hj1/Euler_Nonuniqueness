import EulerNonuniqueness.Section6.SourcePacketActualBlockVelocityBudget
import EulerNonuniqueness.Section6.SourcePacketObservationSpatialGeometry
import EulerNonuniqueness.Section6.SourcePacketVelocityWeightedBudget
import EulerNonuniqueness.Section6.SourcePacketActualOutgoingNeutralArbitrary

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000

private theorem local_observation_velocity_unscale
    {weight distance velocityIntegral coefficient neutralIntegral length distanceIntegral correction : ℝ}
    (weightPositive : 0 < weight) (distancePositive : 0 < distance)
    (bound : weight * velocityIntegral ≤ coefficient *
      (weight * (4 * neutralIntegral) / (distance / 2) ^ 2 + length * weight * distanceIntegral / (distance / 2) ^ 3) + correction) :
    velocityIntegral / distance ≤ coefficient *
      (4 * neutralIntegral / (distance / 2) ^ 2 + length * distanceIntegral / (distance / 2) ^ 3) / distance +
      correction / (weight * distance) := by
  have divided := mul_le_mul_of_nonneg_right bound (show 0 ≤ 1 / (weight * distance) by positivity)
  convert divided using 1 <;> field_simp [weightPositive.ne'] <;> ring

private theorem local_observation_velocity_seed_bound
    {circulation length patchRadius omega sourceOmega weight initialDistance distance neutralIntegral distanceIntegral seed : ℝ}
    (circulationPositive : 0 < circulation) (lengthPositive : 0 < length)
    (omegaPositive : 0 < omega) (distancePositive : 0 < distance)
    (sourceLarger : omega ≤ sourceOmega) (weightLarger : omega ≤ weight)
    (initialNonnegative : 0 ≤ initialDistance) (initialBound : initialDistance * omega ≤ sourceOmega)
    (radiusSmall : patchRadius ^ 2 ≤ length ^ 2)
    (circulationIdentity : circulation = 2 * Real.pi * sourceOmega * length ^ 2)
    (neutralBound : (16 * circulation / (Real.pi * distance ^ 3)) * neutralIntegral ≤ seed)
    (distanceBound : distanceIntegral ≤ 3 * length * (sourceOmega / weight ^ 2 + initialDistance / weight))
    (seedIdentity : seed = Real.sqrt 3 * circulation ^ 2 / (2 * Real.sqrt 2 * Real.pi ^ 2 * omega ^ 2 * distance ^ 4)) :
    (40 * circulation / (2 * Real.pi)) *
        (4 * neutralIntegral / (distance / 2) ^ 2 + length * distanceIntegral / (distance / 2) ^ 3) / distance +
      32 * circulation * patchRadius ^ 2 / (Real.pi * (distance / 2) ^ 3) / (weight * distance) ≤ 4096 * seed := by
  have sourcePositive := omegaPositive.trans_le sourceLarger
  have weightPositive := omegaPositive.trans_le weightLarger
  let base := circulation ^ 2 / (Real.pi ^ 2 * omega ^ 2 * distance ^ 4)
  have baseNonnegative : 0 ≤ base := by dsimp only [base]; positivity
  have sqrtTwoUpper : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtThreeLower : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have baseSeed : base ≤ 4 * seed := by
    rw [seedIdentity]
    dsimp only [base]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have factor : 2 * Real.sqrt 2 ≤ 4 * Real.sqrt 3 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right factor
      (show 0 ≤ circulation ^ 2 * (Real.pi ^ 2 * omega ^ 2 * distance ^ 4) by positivity)]
  have seedNonnegative : 0 ≤ seed := by rw [seedIdentity]; positivity
  have inverseWeight : 1 / weight ^ 2 ≤ 1 / omega ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos omegaPositive)
      (pow_le_pow_left₀ omegaPositive.le weightLarger 2)
  have productLower : omega ^ 2 ≤ sourceOmega * weight := by
    exact (show omega ^ 2 = omega * omega by ring).le.trans
      (mul_le_mul sourceLarger weightLarger omegaPositive.le sourcePositive.le)
  have inverseProduct : 1 / (sourceOmega * weight) ≤ 1 / omega ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos omegaPositive) productLower
  have initialTerm : initialDistance / (sourceOmega * weight) ≤ 1 / omega ^ 2 := by
    apply (div_le_div_iff₀ (mul_pos sourcePositive weightPositive) (sq_pos_of_pos omegaPositive)).mpr
    have first := mul_le_mul_of_nonneg_right initialBound omegaPositive.le
    have second := mul_le_mul_of_nonneg_left weightLarger sourcePositive.le
    nlinarith
  have neutralCost : (40 * circulation / (2 * Real.pi)) * (4 * neutralIntegral / (distance / 2) ^ 2) / distance ≤ 20 * seed := by
    convert mul_le_mul_of_nonneg_left neutralBound (by norm_num : (0 : ℝ) ≤ 20) using 1 <;> field_simp <;> ring
  have distanceCost : (40 * circulation / (2 * Real.pi)) * (length * distanceIntegral / (distance / 2) ^ 3) / distance ≤ 480 * base := by
    have comparison := mul_le_mul_of_nonneg_left distanceBound
      (show 0 ≤ (40 * circulation / (2 * Real.pi)) * length / ((distance / 2) ^ 3 * distance) by positivity)
    have identity : (40 * circulation / (2 * Real.pi)) * length / ((distance / 2) ^ 3 * distance) *
        (3 * length * (sourceOmega / weight ^ 2 + initialDistance / weight)) =
        (240 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4)) *
          (1 / weight ^ 2 + initialDistance / (sourceOmega * weight)) := by
      rw [circulationIdentity]
      field_simp
      ring
    rw [identity] at comparison
    have bounded := mul_le_mul_of_nonneg_left (add_le_add inverseWeight initialTerm)
      (show 0 ≤ 240 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4) by positivity)
    convert comparison.trans bounded using 1 <;> dsimp only [base] <;> ring
  have patchCost : 32 * circulation * patchRadius ^ 2 / (Real.pi * (distance / 2) ^ 3) / (weight * distance) ≤ 128 * base := by
    have radiusComparison := mul_le_mul_of_nonneg_left radiusSmall
      (show 0 ≤ 32 * circulation / (Real.pi * (distance / 2) ^ 3 * (weight * distance)) by positivity)
    have identity : 32 * circulation / (Real.pi * (distance / 2) ^ 3 * (weight * distance)) * length ^ 2 =
        (128 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4)) * (1 / (sourceOmega * weight)) := by
      rw [circulationIdentity]
      field_simp
      ring
    rw [identity] at radiusComparison
    have bounded := mul_le_mul_of_nonneg_left inverseProduct
      (show 0 ≤ 128 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4) by positivity)
    convert radiusComparison.trans bounded using 1 <;> dsimp only [base] <;> ring
  have total := add_le_add (add_le_add neutralCost distanceCost) patchCost
  have normalized : (40 * circulation / (2 * Real.pi)) *
        (4 * neutralIntegral / (distance / 2) ^ 2 + length * distanceIntegral / (distance / 2) ^ 3) / distance +
      32 * circulation * patchRadius ^ 2 / (Real.pi * (distance / 2) ^ 3) / (weight * distance) ≤
      20 * seed + 608 * base := by convert total using 1 <;> ring
  exact normalized.trans (by nlinarith)

theorem exists_actual_local_observation_source_velocity_seed_budget :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 8192 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant radiusFactor receiverRadiusFactor initialError : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant → 0 < radiusFactor → 0 < receiverRadiusFactor → initialError ≤ 1 / 64 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ observation : ℝ → ℂ, Continuous observation →
    ∀ start horizon initialDistance outgoingPhase : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    2048 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    12 * initialDistance ≤ scales.ratio →
    20 * initialError + 83200 / initialDistance ^ 2 ≤ 1 / 5120 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ initialError * length →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ initialError * length →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    (∀ time ∈ Icc 0 start, ∀ patch, motion.domain time source patch ⊆
      Metric.closedBall (quadrupoleCenter motion time source) (radiusFactor * length)) →
    (∀ elapsed ∈ Icc 0 horizon, ‖observation elapsed - quadrupoleCenter motion (start + elapsed) receiver‖ ≤
      receiverRadiusFactor * changed.length (receiver.val + 1)) →
    ∃ geometry : SourcePacketPhysicalGeometry prepared.trajectory.movingFamily changed source start horizon 1,
      geometry.location = observation ∧
      geometry.frozenDisplacement = (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ) ∧
      IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
        ‖biotSavart (quadrupoleDensity changed motion (start + elapsed) source) (geometry.location elapsed)‖ /
          ‖geometry.frozenDisplacement‖) volume 0 horizon ∧
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
        ‖biotSavart (quadrupoleDensity changed motion (start + elapsed) source) (geometry.location elapsed)‖ /
          ‖geometry.frozenDisplacement‖) ≤
        4096 * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * ‖geometry.frozenDisplacement‖ ^ 4)) := by
  obtain ⟨radius, radiusPositive, radiusSmall, geometries⟩ := exists_source_packet_blockcenter_reference_frame_geometry
  refine ⟨radius, radiusPositive, radiusSmall, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant radiusFactor receiverRadiusFactor initialError factorPositive factorSmall rootOne boundaryOne
    radiusFactorPositive receiverRadiusPositive initialErrorSmall
  have ratioBound : 2 ≤ scales.ratio := by linarith
  have factorOne : factor ≤ 1 := by linarith
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  have thresholdSmall : threshold ≤ 1 / 2 := (thresholdBound.trans radiusSmall).trans (by norm_num)
  filter_upwards [geometries scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant 1 1 factorPositive factorOne rootOne boundaryOne
      (by norm_num) (by norm_num),
    scales.eventually_actual_outgoing_neutral_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall rootPositive boundaryNonnegative thresholdSmall radiusFactorPositive (tolerance := 1) (by norm_num),
    scales.eventually_actual_posthit_continuation amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne rootPositive boundaryNonnegative,
    scales.eventually_radius_lt_length amplitudePositive (by linarith) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_actual_outgoing_observation_spatial_geometry amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne thresholdSmall rootOne boundaryOne receiverRadiusPositive,
    eventually_ge_atTop (1 : ℝ)] with frequency geometries neutral continuation radii spatial frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent observation observationContinuous start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prehistory observationClose
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let length := changed.length (source.val + 1)
  let omega := changed.omega source.val
  let sourceOmega := changed.omega (source.val + 1)
  let weight := 2 * Real.sqrt 2 * omega
  let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
  let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  let distance := ‖frozen‖
  let seed := Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * omega ^ 2 * distance ^ 4)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have lengthPositive : 0 < length := changed.length_pos _
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have sourcePositive : 0 < sourceOmega := changed.omega_pos frequencyPositive ratioPositive _
  have weightPositive : 0 < weight := by dsimp only [weight]; positivity
  have directionNorm : ‖direction‖ = 1 := by rw [Complex.norm_exp]; simp [direction]
  have different : receiver ≠ source := by intro equality; subst source; omega
  have distancePositive : 0 < distance := by
    dsimp only [distance, frozen]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact changed.location_distance_pos (by omega)
  have distanceOne : distance ≤ 1 := by
    dsimp only [distance, frozen]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith [changed.location_le_one (receiver.val + 1), changed.location_le_one (source.val + 1),
      changed.location_pos (receiver.val + 1), changed.location_pos (source.val + 1)]
  have firstCoarse : ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 :=
    firstInitial.trans (by nlinarith)
  have secondCoarse : ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 :=
    secondInitial.trans (by nlinarith)
  have horizonOne : horizon ≤ 1 := by linarith [path.stopBound]
  obtain ⟨base, normalization⟩ := geometries count phase dipoleAngle prepared path receiver source different
    start horizon initialDistance outgoingPhase startNonnegative horizonNonnegative endBound (by linarith) initialDistanceSmall
    direction directionNorm firstCoarse secondCoarse initialProjection initialUpper
  have observed := spatial count phase dipoleAngle prepared path receiver source different observation
    start horizon initialDistance startNonnegative horizonNonnegative endBound (by linarith) initialDistanceSmall
    direction directionNorm firstCoarse secondCoarse initialProjection initialUpper observationClose
  let geometry : SourcePacketPhysicalGeometry prepared.trajectory.movingFamily changed source start horizon 1 :=
    { base with
      location := observation
      locationContinuous := observationContinuous
      separated := by
        intro elapsed inside patch
        rw [normalization.gap]
        exact (observed.2.2 elapsed inside).1 patch
      far := by
        intro elapsed inside
        rw [normalization.firstCenter, normalization.secondCenter, source_packet_dipole_average_eq_center]
        exact (observed.2.2 elapsed inside).2.2.2.2.1
      observationLower := by
        intro elapsed inside
        rw [normalization.observationDistance, normalization.gap, normalization.firstCenter,
          normalization.secondCenter, source_packet_dipole_average_eq_center]
        exact (observed.2.2 elapsed inside).2.2.2.2.2.1
      displacementClose := by
        intro elapsed inside
        rw [normalization.firstCenter, normalization.secondCenter, source_packet_dipole_average_eq_center,
          normalization.frozenDisplacement]
        exact (observed.2.2 elapsed inside).2.2.2.2.2.2.2 }
  have neutralBound := neutral count phase dipoleAngle prepared path source start horizon initialDistance startNonnegative
    horizonNonnegative horizonOne endBound (by linarith) initialDistanceSmall direction directionNorm firstCoarse secondCoarse
    initialProjection initialUpper prehistory distance distancePositive distanceOne
  simp only [one_mul] at neutralBound
  have outgoing := continuation count phase dipoleAngle prepared path source start horizon initialDistance startNonnegative
    horizonNonnegative horizonOne endBound (by linarith) initialDistanceSmall direction directionNorm firstCoarse secondCoarse
    initialProjection initialUpper
  let deltaIntegral := ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
    ‖centroidAsymmetry motion (start + elapsed) source‖
  let distanceIntegral := ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
    ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖
  let velocityIntegral := ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
    ‖biotSavart (quadrupoleDensity changed motion (start + elapsed) source) (geometry.location elapsed)‖
  have neutralIdentity : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
      ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖) = 4 * deltaIntegral := by
    rw [normalization.firstSeparation, normalization.secondSeparation, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro elapsed _
    dsimp only
    have identity : firstDipoleSeparation motion (start + elapsed) source + secondDipoleSeparation motion (start + elapsed) source =
        4 * centroidAsymmetry motion (start + elapsed) source := by
      dsimp only [firstDipoleSeparation, secondDipoleSeparation, centroidAsymmetry]
      ring
    rw [identity, norm_mul]
    norm_num
    ring
  have distanceContinuous := (geometry.firstCenterContinuous.sub geometry.secondCenterContinuous).norm
  have exponentialContinuous : Continuous (fun elapsed : ℝ => Real.exp (-weight * elapsed)) := by fun_prop
  have affineContinuous : Continuous (fun elapsed : ℝ => Real.exp (-weight * elapsed) *
      (3 * length * sourceOmega * elapsed + 3 * length * initialDistance)) := by fun_prop
  have distanceComparison := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative
    ((exponentialContinuous.mul distanceContinuous).intervalIntegrable 0 horizon) (affineContinuous.intervalIntegrable 0 horizon)
    (fun elapsed inside => by
      have bound := (outgoing elapsed inside).2.2.2
      rw [normalization.firstCenter, normalization.secondCenter]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      convert bound using 1 <;> dsimp only [length, sourceOmega] <;> ring)
  have distanceBound : distanceIntegral ≤ 3 * length * (sourceOmega / weight ^ 2 + initialDistance / weight) := by
    have actual := distanceComparison.trans (laplace_affine_integral_bound weightPositive
      (show 0 ≤ 3 * length * sourceOmega by positivity) (show 0 ≤ 3 * length * initialDistance by positivity) horizonNonnegative)
    convert actual using 1 <;> ring
  obtain ⟨integrable, weighted⟩ := geometry.actual_velocity_weighted_integral_bound horizonNonnegative weightPositive
  rw [neutralIdentity, normalization.halfWidth, normalization.observationDistance, normalization.gap] at weighted
  change weight * velocityIntegral ≤ (40 * changed.circulation (source.val + 1) / (2 * Real.pi)) *
      (weight * (4 * deltaIntegral) / (distance / 2) ^ 2 + length * weight * distanceIntegral / (distance / 2) ^ 3) +
      32 * changed.circulation (source.val + 1) * changed.radius (source.val + 1) ^ 2 / (Real.pi * (distance / 2) ^ 3) at weighted
  have unweighted := local_observation_velocity_unscale weightPositive distancePositive weighted
  have sourceIdentity : sourceOmega = changed.ratio * omega := by dsimp only [sourceOmega, omega, Scales.omega]; rw [pow_succ]; ring
  have sourceLarger : omega ≤ sourceOmega := by
    rw [sourceIdentity]
    exact le_mul_of_one_le_left omegaPositive.le (show 1 ≤ changed.ratio by dsimp only [changed]; linarith)
  have weightLarger : omega ≤ weight := by
    have sqrtLower : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    dsimp only [weight]
    nlinarith [mul_le_mul_of_nonneg_right sqrtLower omegaPositive.le]
  have initialBound : initialDistance * omega ≤ sourceOmega := by
    rw [sourceIdentity]
    exact mul_le_mul_of_nonneg_right (show initialDistance ≤ changed.ratio by dsimp only [changed]; linarith) omegaPositive.le
  have radiusSmall : changed.radius (source.val + 1) ^ 2 ≤ length ^ 2 := by
    have bound := (radii (source.val + 1)).le
    simp only [one_mul] at bound
    exact pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le bound 2
  have scalar := local_observation_velocity_seed_bound (changed.circulation_pos frequencyPositive ratioPositive _)
    lengthPositive omegaPositive distancePositive sourceLarger weightLarger (show 0 ≤ initialDistance by linarith)
    initialBound radiusSmall (by rfl) neutralBound distanceBound (by rfl : seed = _)
  refine ⟨geometry, rfl, normalization.frozenDisplacement, ?_, ?_⟩
  · change IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) *
        ‖biotSavart (quadrupoleDensity changed motion (start + elapsed) source) (geometry.location elapsed)‖ /
          ‖geometry.frozenDisplacement‖) volume 0 horizon
    exact integrable.div_const _
  · rw [intervalIntegral.integral_div, normalization.frozenDisplacement]
    exact unweighted.trans scalar

end EulerNonuniqueness.Paper

