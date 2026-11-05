import EulerNonuniqueness.Section6.SourcePacketCoefficientWeightedBudget
import EulerNonuniqueness.Section6.SourcePacketBlockCenterGeometry
import EulerNonuniqueness.Section6.SourcePacketActualOutgoingNeutralArbitrary
import EulerNonuniqueness.Section5.CascadeIndividualSourcePatchCoefficientContinuity
import EulerNonuniqueness.Section6.ForeignQuadrupoleStrainDerivative

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000

private theorem outgoing_blockcenter_coefficient_seed_bound
    {circulation length patchRadius omega sourceOmega decay initialDistance distance neutralIntegral distanceIntegral seed quotient : ℝ}
    (circulationPositive : 0 < circulation) (lengthPositive : 0 < length)
    (omegaPositive : 0 < omega) (distancePositive : 0 < distance)
    (sourceLarger : omega ≤ sourceOmega) (decayLarger : omega ≤ decay)
    (initialBound : initialDistance * omega ≤ sourceOmega)
    (radiusSmall : patchRadius ^ 2 ≤ length ^ 2)
    (circulationIdentity : circulation = 2 * Real.pi * sourceOmega * length ^ 2)
    (neutralNonnegative : 0 ≤ neutralIntegral) (distanceNonnegative : 0 ≤ distanceIntegral)
    (neutralBound : (16 * circulation / (Real.pi * distance ^ 3)) * neutralIntegral ≤ seed)
    (distanceBound : distanceIntegral ≤ 3 * length * (sourceOmega / decay ^ 2 + initialDistance / decay))
    (seedIdentity : seed = Real.sqrt 3 * circulation ^ 2 / (2 * Real.sqrt 2 * Real.pi ^ 2 * omega ^ 2 * distance ^ 4))
    (quotientSmall : quotient ≤ 1 / 2) :
    (96 * (circulation / (2 * Real.pi)) * (1 - quotient)⁻¹) *
        (4 * (distance / 4)⁻¹ ^ 3 * (4 * neutralIntegral) +
          128 * (distance / 4)⁻¹ ^ 4 * length * distanceIntegral) +
      (256 * 96 * circulation * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi) *
        (1 - quotient)⁻¹ / decay ≤ 1000000000 * seed := by
  have sourcePositive := omegaPositive.trans_le sourceLarger
  have decayPositive := omegaPositive.trans_le decayLarger
  let base := circulation ^ 2 / (Real.pi ^ 2 * omega ^ 2 * distance ^ 4)
  have baseNonnegative : 0 ≤ base := by dsimp only [base]; positivity
  have sqrtTwoUpper : Real.sqrt 2 ≤ 2 := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have sqrtThreeLower : 1 ≤ Real.sqrt 3 := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have baseSeed : base ≤ 4 * seed := by
    rw [seedIdentity]
    dsimp only [base]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have factor : 2 * Real.sqrt 2 ≤ 4 * Real.sqrt 3 := by linarith only [sqrtTwoUpper, sqrtThreeLower]
    nlinarith only [mul_le_mul_of_nonneg_right factor
      (show 0 ≤ circulation ^ 2 * (Real.pi ^ 2 * omega ^ 2 * distance ^ 4) by positivity)]
  have seedNonnegative : 0 ≤ seed := by rw [seedIdentity]; positivity
  have inverseDecay : 1 / decay ^ 2 ≤ 1 / omega ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos omegaPositive)
      (pow_le_pow_left₀ omegaPositive.le decayLarger 2)
  have productLower : omega ^ 2 ≤ sourceOmega * decay := by
    exact (show omega ^ 2 = omega * omega by ring).le.trans
      (mul_le_mul sourceLarger decayLarger omegaPositive.le sourcePositive.le)
  have inverseProduct : 1 / (sourceOmega * decay) ≤ 1 / omega ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos omegaPositive) productLower
  have initialTerm : initialDistance / (sourceOmega * decay) ≤ 1 / omega ^ 2 := by
    apply (div_le_div_iff₀ (mul_pos sourcePositive decayPositive) (sq_pos_of_pos omegaPositive)).mpr
    have first := mul_le_mul_of_nonneg_right initialBound omegaPositive.le
    have second := mul_le_mul_of_nonneg_left decayLarger sourcePositive.le
    nlinarith only [first, second]
  have inverseBound : (1 - quotient)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ (show 0 < 1 - quotient by linarith only [quotientSmall])).mpr
    linarith only [quotientSmall]
  have majorized := add_le_add
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left inverseBound (show 0 ≤ 96 * (circulation / (2 * Real.pi)) by positivity))
      (show 0 ≤ 4 * (distance / 4)⁻¹ ^ 3 * (4 * neutralIntegral) +
        128 * (distance / 4)⁻¹ ^ 4 * length * distanceIntegral by positivity))
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left inverseBound
        (show 0 ≤ 256 * 96 * circulation * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi by positivity))
      decayPositive.le)
  have neutralCost : (96 * (circulation / (2 * Real.pi)) * 2) *
      (4 * (distance / 4)⁻¹ ^ 3 * (4 * neutralIntegral)) ≤ 6144 * seed := by
    convert mul_le_mul_of_nonneg_left neutralBound (by norm_num : (0 : ℝ) ≤ 6144) using 1 <;> field_simp <;> ring
  have distanceCost : (96 * (circulation / (2 * Real.pi)) * 2) *
      (128 * (distance / 4)⁻¹ ^ 4 * length * distanceIntegral) ≤ 9437184 * base := by
    have comparison := mul_le_mul_of_nonneg_left distanceBound
      (show 0 ≤ 3145728 * circulation * length / (Real.pi * distance ^ 4) by positivity)
    have identity : (3145728 * circulation * length / (Real.pi * distance ^ 4)) *
        (3 * length * (sourceOmega / decay ^ 2 + initialDistance / decay)) =
        (4718592 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4)) *
          (1 / decay ^ 2 + initialDistance / (sourceOmega * decay)) := by
      rw [circulationIdentity]
      field_simp
      ring
    rw [identity] at comparison
    have bounded := mul_le_mul_of_nonneg_left (add_le_add inverseDecay initialTerm)
      (show 0 ≤ 4718592 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4) by positivity)
    convert comparison.trans bounded using 1 <;> dsimp only [base] <;> field_simp <;> ring
  have patchCost : (256 * 96 * circulation * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi) * 2 / decay ≤
      6291456 * base := by
    have comparison := mul_le_mul_of_nonneg_left radiusSmall
      (show 0 ≤ 12582912 * circulation / (Real.pi * distance ^ 4 * decay) by positivity)
    have identity : (12582912 * circulation / (Real.pi * distance ^ 4 * decay)) * length ^ 2 =
        (6291456 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4)) * (1 / (sourceOmega * decay)) := by
      rw [circulationIdentity]
      field_simp
      ring
    rw [identity] at comparison
    have bounded := mul_le_mul_of_nonneg_left inverseProduct
      (show 0 ≤ 6291456 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4) by positivity)
    convert comparison.trans bounded using 1 <;> dsimp only [base] <;> field_simp <;> ring
  have total := add_le_add (add_le_add neutralCost distanceCost) patchCost
  apply majorized.trans
  have normalized : (96 * (circulation / (2 * Real.pi)) * 2) *
      (4 * (distance / 4)⁻¹ ^ 3 * (4 * neutralIntegral) +
        128 * (distance / 4)⁻¹ ^ 4 * length * distanceIntegral) +
      (256 * 96 * circulation * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi) * 2 / decay ≤
        6144 * seed + 15728640 * base := by convert total using 1 <;> ring
  exact normalized.trans (by nlinarith only [baseSeed, seedNonnegative])

private theorem outgoing_blockcenter_coefficient_decay_unscale
    {decay integral prefactor neutralCoefficient distanceCoefficient neutralIntegral distanceIntegral correction : ℝ}
    (decayPositive : 0 < decay)
    (bound : decay * integral ≤ prefactor *
      (neutralCoefficient * decay * neutralIntegral + distanceCoefficient * decay * distanceIntegral) + correction) :
    integral ≤ prefactor * (neutralCoefficient * neutralIntegral + distanceCoefficient * distanceIntegral) + correction / decay := by
  apply (mul_le_mul_left decayPositive).mp
  convert bound using 1 <;> field_simp [decayPositive.ne'] <;> ring

theorem exists_actual_blockcenter_source_coefficient_seed_budget :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧ ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 8192 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant radiusFactor initialError : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant → 0 < radiusFactor → initialError ≤ 1 / 64 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val + 1 = source.val →
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
    ∀ receiverRadius : ℝ, 0 ≤ receiverRadius →
    receiverRadius ≤ changed.location (source.val + 1) / (100000 * 96) →
    let distance := changed.location (source.val + 1)
    let decay := 2 * Real.sqrt 2 * changed.omega source.val
    let coefficient := fun (power : ℕ) (elapsed : ℝ) =>
      (prepared.trajectory.movingFamily.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => quadrupoleCenter motion time receiver) receiverRadius (power + 1) (start + elapsed)
    let series := fun elapsed => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖
    (∀ power : ℕ, ContinuousOn (coefficient power) (Icc 0 horizon)) ∧
    (∀ elapsed ∈ Icc 0 horizon, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖)) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * series elapsed) volume 0 horizon ∧
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * series elapsed) ≤
        constant * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)) := by
  obtain ⟨radius, radiusPositive, radiusSmall, geometries⟩ := exists_source_packet_blockcenter_reference_frame_geometry
  refine ⟨radius, radiusPositive, radiusSmall, 1000000000, by norm_num, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant radiusFactor initialError factorPositive factorSmall rootOne boundaryOne
    radiusFactorPositive initialErrorSmall
  have ratioBound : 2 ≤ scales.ratio := by linarith
  have factorOne : factor ≤ 1 := by linarith
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  filter_upwards [geometries scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant 1 1 factorPositive factorOne rootOne boundaryOne
      (by norm_num) (by norm_num),
    scales.eventually_actual_outgoing_neutral_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall rootPositive boundaryNonnegative (thresholdSmall.trans (by norm_num)) radiusFactorPositive
      (tolerance := 1) (by norm_num),
    scales.eventually_actual_posthit_continuation amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne rootPositive boundaryNonnegative,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)]
    with frequency geometries neutral continuation radii frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prehistory receiverRadius receiverNonnegative receiverSmall
  let changed : Scales := {scales with frequency := frequency}
  let family := prepared.trajectory.movingFamily
  let motion := family.patchMotion
  let length := changed.length (source.val + 1)
  let omega := changed.omega source.val
  let sourceOmega := changed.omega (source.val + 1)
  let decay := 2 * Real.sqrt 2 * omega
  let distance := changed.location (source.val + 1)
  let seed := Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * omega ^ 2 * distance ^ 4)
  let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive : 0 < length := changed.length_pos _
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have sourcePositive : 0 < sourceOmega := changed.omega_pos frequencyPositive ratioPositive _
  have decayPositive : 0 < decay := by dsimp only [decay]; positivity
  have distancePositive : 0 < distance := changed.location_pos _
  have distanceOne : distance ≤ 1 := changed.location_le_one _
  have directionNorm : ‖direction‖ = 1 := by rw [Complex.norm_exp]; simp [direction]
  have different : receiver ≠ source := by intro same; subst source; omega
  have horizonOne : horizon ≤ 1 := by linarith [path.stopBound]
  have firstCoarse : ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 :=
    firstInitial.trans (by
      have bound := mul_le_mul_of_nonneg_right initialErrorSmall lengthPositive.le
      nlinarith only [bound])
  have secondCoarse : ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 :=
    secondInitial.trans (by
      have bound := mul_le_mul_of_nonneg_right initialErrorSmall lengthPositive.le
      nlinarith only [bound])
  obtain ⟨geometry, normalization⟩ := geometries count phase dipoleAngle prepared path receiver source different
    start horizon initialDistance outgoingPhase startNonnegative horizonNonnegative endBound (by linarith) initialDistanceSmall
    direction directionNorm firstCoarse secondCoarse initialProjection initialUpper
  have frozenNorm : ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ = distance := by
    dsimp only [distance]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← adjacent]
    exact changed.adjacent_location_distance (receiver.val + 1)
  have gapIdentity : geometry.gap = distance / 2 := by rw [normalization.gap, frozenNorm]
  have observationIdentity : geometry.observationDistance = distance / 2 := by
    rw [normalization.observationDistance, gapIdentity]
  have locationCurve : (fun time => geometry.location (time - start)) =
      (fun time => quadrupoleCenter motion time receiver) := by
    with_reducible_and_instances
      funext time
      have actual := congrFun normalization.location (time - start)
      simpa only [show start + (time - start) = time by ring] using actual
  have insideStop (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have sourceCenters (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (label : Fin 4) :
      (family.patch (finProdFinEquiv (source, label))).center (start + elapsed) =
        patchCentroid motion (start + elapsed) source label :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside _ (insideStop elapsed inside)) source label
  have sourceRadii (label : Fin 4) : (family.patch (finProdFinEquiv (source, label))).radius = changed.radius (source.val + 1) :=
    prepared.radiusIdentity source label
  have quotientSmall : 4 * 96 * receiverRadius / (distance / 4) ≤ 1 / 2 := by
    apply (div_le_iff₀ (show 0 < distance / 4 by positivity)).mpr
    nlinarith only [receiverSmall, distancePositive]
  have coefficientsContinuous (power : ℕ) : ContinuousOn (fun elapsed =>
      (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => geometry.location (time - start)) receiverRadius (power + 1) (start + elapsed)) (Icc 0 horizon) := by
    rw [locationCurve]
    have coefficientContinuous : ContinuousOn ((family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => quadrupoleCenter motion time receiver) receiverRadius (power + 1)) (Icc start (start + horizon)) := by
      apply (family.quadrupoleSubfamily source).exteriorTaylorCoefficient_continuousOn_of_local_center_gaps
        Finset.univ _ receiverRadius (power + 1) _ (show 0 < distance / 8 by positivity)
        (fun time inside => family.quadrupoleCenter_contDiffAt receiver (fun _ => globalInside time
          ⟨by linarith [inside.1], by linarith [inside.2]⟩))
        (fun time inside _ _ => globalInside time ⟨by linarith [inside.1], by linarith [inside.2]⟩)
      intro time inside label _
      have elapsedInside : time - start ∈ Icc 0 horizon := ⟨by linarith [inside.1], by linarith [inside.2]⟩
      have clearance := geometry.separated (time - start) elapsedInside label
      rw [normalization.location, gapIdentity] at clearance
      dsimp only at clearance
      have timeIdentity : start + (time - start) = time := by ring
      rw [timeIdentity] at clearance
      have small := geometry.radiusSmall
      rw [gapIdentity] at small
      change distance / 8 + 3 * (family.patch (finProdFinEquiv (source, label))).radius ≤
        ‖quadrupoleCenter motion time receiver - (family.patch (finProdFinEquiv (source, label))).center time‖
      rw [sourceRadii]
      have center := sourceCenters (time - start) elapsedInside label
      rw [timeIdentity] at center
      rw [center]
      linarith only [small, clearance]
    exact coefficientContinuous.comp (continuous_const.add continuous_id).continuousOn
      (fun elapsed inside => ⟨by linarith [inside.1], by linarith [inside.2]⟩)
  obtain ⟨integrable, weighted⟩ := geometry.actual_outgoing_coefficient_series_weighted_integral_bound
    horizonNonnegative sourceRadii sourceCenters receiverNonnegative (show 0 < distance / 4 by positivity)
    (by norm_num : (0 : ℝ) ≤ 96) decayPositive
    (by rw [gapIdentity]; linarith) (by rw [observationIdentity]; linarith)
    (quotientSmall.trans_lt (by norm_num)) coefficientsContinuous
  dsimp only at integrable weighted
  rw [locationCurve] at integrable weighted
  have neutralBound := neutral count phase dipoleAngle prepared path source start horizon initialDistance startNonnegative
    horizonNonnegative horizonOne endBound (by linarith) initialDistanceSmall direction directionNorm firstCoarse secondCoarse
    initialProjection initialUpper prehistory distance distancePositive distanceOne
  simp only [one_mul] at neutralBound
  have outgoing := continuation count phase dipoleAngle prepared path source start horizon initialDistance startNonnegative
    horizonNonnegative horizonOne endBound (by linarith) initialDistanceSmall direction directionNorm firstCoarse secondCoarse
    initialProjection initialUpper
  let neutralIntegral := ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
    ‖centroidAsymmetry motion (start + elapsed) source‖
  let distanceIntegral := ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
    ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖
  have neutralIdentity : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖) = 4 * neutralIntegral := by
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
  have exponentialContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed)) := by fun_prop
  have affineContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed) *
      (3 * length * sourceOmega * elapsed + 3 * length * initialDistance)) := by fun_prop
  have distanceComparison := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative
    ((exponentialContinuous.mul distanceContinuous).intervalIntegrable 0 horizon) (affineContinuous.intervalIntegrable 0 horizon)
    (fun elapsed inside => by
      have bound := (outgoing elapsed inside).2.2.2
      rw [normalization.firstCenter, normalization.secondCenter]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      convert bound using 1 <;> dsimp only [length, sourceOmega] <;> ring)
  have distanceBound : distanceIntegral ≤ 3 * length * (sourceOmega / decay ^ 2 + initialDistance / decay) := by
    have actual := distanceComparison.trans (laplace_affine_integral_bound decayPositive
      (show 0 ≤ 3 * length * sourceOmega by positivity) (show 0 ≤ 3 * length * initialDistance by positivity) horizonNonnegative)
    convert actual using 1 <;> ring
  rw [neutralIdentity, normalization.halfWidth] at weighted
  have unweighted : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖(family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun time => quadrupoleCenter motion time receiver) receiverRadius (power + 1) (start + elapsed)‖) ≤
      (96 * (changed.circulation (source.val + 1) / (2 * Real.pi)) *
          (1 - 4 * 96 * receiverRadius / (distance / 4))⁻¹) *
        (4 * (distance / 4)⁻¹ ^ 3 * (4 * neutralIntegral) +
          128 * (distance / 4)⁻¹ ^ 4 * length * distanceIntegral) +
      (256 * 96 * changed.circulation (source.val + 1) * changed.radius (source.val + 1) ^ 2 *
        (distance / 4)⁻¹ ^ 4 / Real.pi) *
          (1 - 4 * 96 * receiverRadius / (distance / 4))⁻¹ / decay := by
    have actual := outgoing_blockcenter_coefficient_decay_unscale decayPositive weighted
    simpa only [length, distanceIntegral, changed] using actual
  have sourceIdentity : sourceOmega = changed.ratio * omega := by
    dsimp only [sourceOmega, omega, Scales.omega]
    rw [pow_succ]
    ring
  have sourceLarger : omega ≤ sourceOmega := by
    rw [sourceIdentity]
    exact le_mul_of_one_le_left omegaPositive.le (show 1 ≤ changed.ratio by change 1 ≤ scales.ratio; linarith)
  have decayLarger : omega ≤ decay := by
    have sqrtLower : 1 ≤ Real.sqrt 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    change omega ≤ (2 * Real.sqrt 2) * omega
    exact le_mul_of_one_le_left omegaPositive.le (by linarith only [sqrtLower])
  have initialBound : initialDistance * omega ≤ sourceOmega := by
    rw [sourceIdentity]
    exact mul_le_mul_of_nonneg_right (show initialDistance ≤ changed.ratio by
      change initialDistance ≤ scales.ratio
      linarith only [ratioBudget, initialDistanceLarge])
      omegaPositive.le
  have radiusSmall : changed.radius (source.val + 1) ^ 2 ≤ length ^ 2 := by
    have bound := (radii (source.val + 1)).le
    simp only [one_mul] at bound
    exact pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le bound 2
  have scalar := outgoing_blockcenter_coefficient_seed_bound (changed.circulation_pos frequencyPositive ratioPositive _)
    lengthPositive omegaPositive distancePositive sourceLarger decayLarger initialBound radiusSmall (by rfl)
    (intervalIntegral.integral_nonneg_of_forall horizonNonnegative (fun _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)))
    (intervalIntegral.integral_nonneg_of_forall horizonNonnegative (fun _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)))
    neutralBound distanceBound (by rfl : seed = _) quotientSmall
  refine ⟨?_, ?_, integrable, unweighted.trans scalar⟩
  · intro power
    simpa only [locationCurve] using coefficientsContinuous power
  · intro elapsed inside
    have actual := geometry.actual_outgoing_coefficient_series_summable_and_tsum_le inside sourceRadii
      (sourceCenters elapsed inside) receiverNonnegative (show 0 < distance / 4 by positivity)
      (by norm_num : (0 : ℝ) ≤ 96) (by rw [gapIdentity]; linarith) (by rw [observationIdentity]; linarith)
      (quotientSmall.trans_lt (by norm_num))
    simpa only [locationCurve] using actual.1

end EulerNonuniqueness.Paper


