import EulerNonuniqueness.Section6.SourcePacketLocalObservationVelocityBudget
import EulerNonuniqueness.Section6.SourcePacketReferenceVelocityWindow
import EulerNonuniqueness.Section5.CascadePrehitCentroidExtent

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 750000

private theorem prehit_velocity_half_distance_transport {integral distance numerator denominator coefficient : ℝ}
    (distancePositive : 0 < distance) (denominatorPositive : 0 < denominator)
    (bound : integral / (distance / 2) ≤ coefficient * (numerator / (denominator * (distance / 2) ^ 4))) :
    integral / distance ≤ 8 * coefficient * (numerator / (denominator * distance ^ 4)) := by
  have scaled := mul_le_mul_of_nonneg_left bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert scaled using 1 <;> field_simp [distancePositive.ne', denominatorPositive.ne'] <;> ring

theorem exists_actual_prehit_patch_source_velocity_seed_budget :
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
    let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ initialError * length →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ initialError * length →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    (∀ time ∈ Icc 0 start, ∀ patch, motion.domain time source patch ⊆
      Metric.closedBall (quadrupoleCenter motion time source) (radiusFactor * length)) →
    (∀ time ∈ Icc 0 (start + horizon), |radialShape motion time receiver| ≤ 1 / 2) →
    ∀ patch : Fin 4,
    let distance := changed.location (source.val + 1)
    let field := fun elapsed =>
      biotSavart (quadrupoleDensity changed motion (start + elapsed) source)
          (patchCentroid motion (start + elapsed) receiver patch) -
        biotSavart (quadrupoleDensity changed reference (start + elapsed) source)
          (patchCentroid reference (start + elapsed) receiver patch)
    IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
      ‖field elapsed‖ / distance) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
      ‖field elapsed‖ / distance) ≤
      constant * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)) := by
  obtain ⟨radius, radiusPositive, radiusSmall, alternative⟩ := exists_actual_local_observation_source_velocity_seed_budget
  obtain ⟨referenceCoefficient, referenceCoefficientNonnegative, references⟩ := exists_uniform_reference_velocity_window_seed_budget
  let constant := 4096 + 8 * (referenceCoefficient + 1)
  refine ⟨radius, radiusPositive, radiusSmall, constant, by dsimp only [constant]; positivity, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant radiusFactor initialError factorPositive factorSmall rootOne boundaryOne
    radiusFactorPositive initialErrorSmall
  have ratioBound : 2 ≤ scales.ratio := by linarith
  have ratioPositive : 0 < scales.ratio := by linarith
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  filter_upwards [alternative scales amplitudePositive ratioLarge alphaPositive referenceConstant referenceNonnegative amplitudeBound
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant radiusFactor 3 initialError factorPositive factorSmall
      rootOne boundaryOne radiusFactorPositive (by norm_num) initialErrorSmall,
    references scales amplitudePositive ratioLarge alphaPositive referenceConstant (1 / 2) (1 / scales.ratio)
      referenceNonnegative (by norm_num) (by positivity),
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive
      (by linarith : 0 < scaleRoot) (by linarith : 0 ≤ boundaryConstant) thresholdSmall referenceNonnegative,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    eventually_gt_atTop (0 : ℝ)]
    with frequency alternative references extents alignment frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prehistory radialSmall patch
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let decay := 2 * Real.sqrt 2 * changed.omega source.val
  let distance := changed.location (source.val + 1)
  let seed := Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)
  let observation := fun elapsed => patchCentroid motion (start + elapsed) receiver patch
  let referenceLocation := fun elapsed => patchCentroid reference (start + elapsed) receiver patch
  have distancePositive : 0 < distance := changed.location_pos _
  have different : receiver ≠ source := by intro equality; subst source; omega
  have nonterminal : receiver.val + 1 < count := by omega
  have timeContinuous : Continuous (fun elapsed : ℝ => start + elapsed) := continuous_const.add continuous_id
  have observationContinuous : Continuous observation :=
    (prepared.trajectory.movingFamily.patchCentroid_continuous receiver patch).comp timeContinuous
  have referenceLocationContinuous : Continuous referenceLocation :=
    (prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous receiver patch).comp timeContinuous
  have observationClose : ∀ elapsed ∈ Icc 0 horizon,
      ‖observation elapsed - quadrupoleCenter motion (start + elapsed) receiver‖ ≤
        3 * changed.length (receiver.val + 1) := by
    intro elapsed inside
    exact (extents prepared path factorSmall receiver nonterminal (start + horizon) (by linarith) endBound radialSmall
      (start + elapsed) ⟨by linarith [inside.1], by linarith [inside.2]⟩ patch).1
  obtain ⟨geometry, locationIdentity, frozenIdentity, alternativeIntegrable, alternativeBound⟩ :=
    alternative count phase dipoleAngle prepared path receiver source adjacent observation observationContinuous
      start horizon initialDistance outgoingPhase startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall
      ratioBudget initialBudget firstInitial secondInitial initialProjection initialUpper prehistory observationClose
  have frozen : ‖geometry.frozenDisplacement‖ = distance := by
    dsimp only [distance]
    rw [frozenIdentity, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← adjacent]
    exact changed.adjacent_location_distance (receiver.val + 1)
  have realFrozen : |changed.location (receiver.val + 1) - changed.location (source.val + 1)| = distance := by
    simpa only [frozenIdentity, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using frozen
  have windowBound : start + horizon ≤ 2 := by linarith [path.stopBound]
  obtain ⟨referenceIntegrableHalf, referenceBoundHalf⟩ := references prepared.referenceWitness.trajectory.movingFamily
    prepared.referenceWitness.densityIdentity prepared.referenceWitness.evolution (thresholdSmall.trans (by norm_num)) prepared.referenceWitness.coarse
    startNonnegative horizonNonnegative windowBound source referenceLocation referenceLocationContinuous.measurable
    (distance := distance / 2) (by positivity) (by have one := changed.location_le_one (source.val + 1); dsimp only [distance]; linarith)
    (by dsimp only [distance, changed]; ring_nf; exact le_rfl)
    (by
      intro elapsed inside
      have fullInside : start + elapsed ∈ Icc 0 path.stop := ⟨by linarith [inside.1], by linarith [inside.2]⟩
      have actual := (alignment count phase dipoleAngle prepared path (start + elapsed) fullInside (receiver, patch) source different).1
      change ‖(referenceLocation elapsed - quadrupoleCenter reference (start + elapsed) source) -
        ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))‖ ≤
          3 * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 16 at actual
      have triangle := norm_add_le
        (referenceLocation elapsed - quadrupoleCenter reference (start + elapsed) source)
        (-((referenceLocation elapsed - quadrupoleCenter reference (start + elapsed) source) -
          ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))))
      have identity : (referenceLocation elapsed - quadrupoleCenter reference (start + elapsed) source) +
          -((referenceLocation elapsed - quadrupoleCenter reference (start + elapsed) source) -
            ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))) =
          (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ) := by abel
      rw [identity, norm_neg, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, realFrozen] at triangle
      simp only [Complex.ofReal_sub] at triangle
      rw [realFrozen] at actual
      change distance / 2 ≤ ‖referenceLocation elapsed - quadrupoleCenter reference (start + elapsed) source‖
      linarith)
  let firstField := fun elapsed => biotSavart (quadrupoleDensity changed motion (start + elapsed) source) (observation elapsed)
  let secondField := fun elapsed => biotSavart (quadrupoleDensity changed reference (start + elapsed) source) (referenceLocation elapsed)
  have referenceIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * ‖secondField elapsed‖ / distance)
      volume 0 horizon := by
    have actual := referenceIntegrableHalf.const_mul (1 / 2 : ℝ)
    convert actual using 1
    ext elapsed
    ring
  have referenceBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖secondField elapsed‖ / distance) ≤
      8 * (referenceCoefficient + 1) * seed := by
    rw [intervalIntegral.integral_div] at referenceBoundHalf ⊢
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive source.val
    have denominatorPositive : 0 < 2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 := by positivity
    have transported := prehit_velocity_half_distance_transport distancePositive denominatorPositive referenceBoundHalf
    have inverseRatio : 1 / scales.ratio ≤ 1 := (div_le_iff₀ ratioPositive).mpr (by linarith)
    have coefficientBound : referenceCoefficient / scales.ratio + 1 / scales.ratio ≤ referenceCoefficient + 1 := by
      have actual := add_le_add (mul_le_mul_of_nonneg_left inverseRatio referenceCoefficientNonnegative) inverseRatio
      convert actual using 1 <;> ring
    have seedNonnegative : 0 ≤ seed := by dsimp only [seed]; positivity
    exact transported.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left coefficientBound (by norm_num)) seedNonnegative)
  rw [frozen, locationIdentity] at alternativeIntegrable alternativeBound
  have firstMeasurable : Measurable firstField := by
    have joint := measurable_biotSavart_of_measurable_vorticity (Parameter := ℝ)
      (vorticity := fun time => quadrupoleDensity changed motion time source)
      (prepared.trajectory.movingFamily.measurable_quadrupoleDensity changed prepared.densityIdentity source)
    simpa only [firstField, Function.comp_def] using joint.comp (timeContinuous.measurable.prodMk observationContinuous.measurable)
  have secondMeasurable : Measurable secondField := by
    have joint := measurable_biotSavart_of_measurable_vorticity (Parameter := ℝ)
      (vorticity := fun time => quadrupoleDensity changed reference time source)
      (prepared.referenceWitness.trajectory.movingFamily.measurable_quadrupoleDensity changed prepared.referenceWitness.densityIdentity source)
    simpa only [secondField, Function.comp_def] using joint.comp (timeContinuous.measurable.prodMk referenceLocationContinuous.measurable)
  have exponentialContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed)) := by fun_prop
  have pairedMeasurable : Measurable (fun elapsed => Real.exp (-decay * elapsed) * ‖firstField elapsed - secondField elapsed‖ / distance) :=
    (exponentialContinuous.measurable.mul (firstMeasurable.sub secondMeasurable).norm).div_const distance
  have pointwise (elapsed : ℝ) : Real.exp (-decay * elapsed) * ‖firstField elapsed - secondField elapsed‖ / distance ≤
      Real.exp (-decay * elapsed) * ‖firstField elapsed‖ / distance + Real.exp (-decay * elapsed) * ‖secondField elapsed‖ / distance := by
    have actual := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (norm_sub_le (firstField elapsed) (secondField elapsed)) (Real.exp_pos (-decay * elapsed)).le) distancePositive.le
    convert actual using 1 <;> ring
  have majorantIntegrable := alternativeIntegrable.add referenceIntegrable
  have pairedIntegrable := majorantIntegrable.mono_fun' pairedMeasurable.aestronglyMeasurable.restrict (by
    rw [uIoc_of_le horizonNonnegative]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) distancePositive.le)]
    exact pointwise elapsed)
  have integralBound := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative pairedIntegrable majorantIntegrable
    (fun elapsed _ => pointwise elapsed)
  rw [intervalIntegral.integral_add alternativeIntegrable referenceIntegrable] at integralBound
  have result := integralBound.trans (add_le_add alternativeBound referenceBound)
  refine ⟨pairedIntegrable, ?_⟩
  convert result using 1 <;> dsimp only [constant, seed] <;> ring

end EulerNonuniqueness.Paper
