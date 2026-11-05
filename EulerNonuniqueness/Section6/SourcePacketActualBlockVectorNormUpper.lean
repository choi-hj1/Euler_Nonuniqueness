import EulerNonuniqueness.Section6.SourcePacketPairedVectorNormUpper
import EulerNonuniqueness.Section6.SourcePacketBlockCenterPhysicalCost
import EulerNonuniqueness.Section6.SourcePacketReferenceBlockCenterBudget
import EulerNonuniqueness.Section6.PaperRelativeLeadingStrainSum

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem SourcePacketBlockCenterNormalization.pairedShapeInput_eq_relativeBlockSourceShapeInput
    {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
    {start horizon chartRadius : ℝ}
    {geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius}
    {reference : PatchMotion count} {receiver : Fin count} {phase : Fin count → ℝ}
    {outgoingPhase deformation : ℝ}
    (normalization : SourcePacketBlockCenterNormalization geometry reference receiver phase outgoingPhase deformation)
    (elapsed : ℝ) :
    geometry.pairedShapeInput (fun current => vorticityComplexStrain
      (quadrupoleDensity scales reference (start + current) source) (quadrupoleCenter reference (start + current) receiver)) elapsed =
      relativeBlockSourceShapeInput scales family.patchMotion reference receiver source (start + elapsed) := by
  unfold SourcePacketPhysicalGeometry.pairedShapeInput SourcePacketPhysicalGeometry.actualStrain
  rw [normalization.location, normalization.positive, normalization.negative]
  rfl

theorem exists_actual_blockcenter_paired_source_vector_norm_upper :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
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
    12 * initialDistance ≤ scales.ratio → 20 * initialError + 83200 / initialDistance ^ 2 ≤ 1 / 5120 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    let input := fun elapsed => relativeBlockSourceShapeInput changed motion reference receiver source (start + elapsed)
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ initialError * length →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ initialError * length →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    (∀ time ∈ Icc 0 start, ∀ label, motion.domain time source label ⊆
      closedBall (quadrupoleCenter motion time source) (radiusFactor * length)) →
    IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) * ‖input elapsed‖) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) * ‖input elapsed‖) ≤
      8 * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 *
          ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ ^ 4)) := by
  obtain ⟨radius, radiusPositive, radiusSmall, physical⟩ := exists_source_packet_blockcenter_reference_frame_physical_cost
  obtain ⟨chartRadius, chartPositive, normUpper⟩ := exists_source_packet_paired_vector_norm_upper
  refine ⟨radius, radiusPositive, radiusSmall, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall
  have ratioBound : 2 ≤ scales.ratio := by linarith
  have factorOne : factor ≤ 1 := by linarith
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  have referenceRatio : max 2 (8192 / (1 : ℝ)) ≤ scales.ratio := by norm_num; exact ratioLarge
  filter_upwards [physical scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
      orbit sectionTime factor scaleRoot boundaryConstant 1 radiusFactor 0 chartRadius 1 initialError
      factorPositive factorSmall rootOne boundaryOne (by norm_num) radiusFactorPositive (by norm_num) chartPositive (by norm_num) initialErrorSmall,
    scales.eventually_actual_inherited_moment_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne rootPositive boundaryNonnegative (by norm_num : (0 : ℝ) < 1),
    scales.eventually_reference_blockcenter_source_frozen_budget amplitudePositive alphaPositive (by norm_num : (0 : ℝ) < 1)
      referenceRatio referenceNonnegative,
    eventually_ge_atTop (1 : ℝ)] with frequency physical inherited referenceBudget frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prefixBounded
  let changed : Scales := {scales with frequency := frequency}
  let family := prepared.trajectory.movingFamily
  let motion := family.patchMotion
  let referenceFamily := prepared.referenceWitness.trajectory.movingFamily
  let reference := referenceFamily.patchMotion
  let length := changed.length (source.val + 1)
  let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
  let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  let referenceStrain := fun elapsed => vorticityComplexStrain (quadrupoleDensity changed reference (start + elapsed) source)
    (quadrupoleCenter reference (start + elapsed) receiver)
  let input := fun elapsed => relativeBlockSourceShapeInput changed motion reference receiver source (start + elapsed)
  let seed := Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * ‖frozen‖ ^ 4)
  have directionNorm : ‖direction‖ = 1 := by rw [Complex.norm_exp]; simp [direction]
  obtain ⟨geometry, normalization, physicalIntegrable, physicalBound⟩ := physical count phase dipoleAngle prepared path receiver source adjacent
    start horizon initialDistance outgoingPhase startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget
    (by simpa only [min_self] using initialBudget)
    firstInitial secondInitial initialProjection initialUpper prefixBounded
  have frozenNonzero : frozen ≠ 0 := by
    simpa only [normalization.frozenDisplacement, frozen, changed] using geometry.frozenNonzero
  have firstCoarse : ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 :=
    firstInitial.trans (by have actual := mul_le_mul_of_nonneg_right initialErrorSmall (changed.length_pos (source.val + 1)).le; convert actual using 1 <;> ring)
  have secondCoarse : ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 :=
    secondInitial.trans (by have actual := mul_le_mul_of_nonneg_right initialErrorSmall (changed.length_pos (source.val + 1)).le; convert actual using 1 <;> ring)
  have inheritedBound := inherited count phase dipoleAngle prepared path source start ⟨startNonnegative, by linarith⟩ initialDistance
    (by linarith) (by simpa only [one_mul] using ratioBudget) direction frozen directionNorm frozenNonzero firstCoarse secondCoarse initialUpper
  have thresholdSmall : threshold ≤ 1 / 4 := (thresholdBound.trans radiusSmall).trans (by norm_num)
  obtain ⟨referenceIntegrable, referenceBound⟩ := referenceBudget prepared.referenceWitness thresholdSmall receiver source adjacent start horizon
    startNonnegative horizonNonnegative (by linarith [path.stopBound])
  have referenceMeasurable : Measurable referenceStrain :=
    (referenceFamily.measurable_quadrupole_strain_along changed prepared.referenceWitness.densityIdentity source
      (referenceFamily.quadrupoleCenter_continuous receiver).measurable).comp (measurable_const.add measurable_id)
  have targetEquation (elapsed : ℝ) := congrFun normalization.targetMoment elapsed
  obtain ⟨integrable, bounded⟩ := normUpper geometry referenceStrain referenceMeasurable outgoingPhase 1 1 1 horizonNonnegative
    targetEquation (by simpa only [normalization.frozenDisplacement, one_mul] using inheritedBound)
    physicalIntegrable (by simpa only [normalization.frozenDisplacement, one_mul] using physicalBound)
    referenceIntegrable (by simpa only [normalization.frozenDisplacement, one_mul] using referenceBound)
  have inputEquation : geometry.pairedShapeInput referenceStrain = input := by
    funext elapsed
    exact normalization.pairedShapeInput_eq_relativeBlockSourceShapeInput elapsed
  rw [inputEquation] at integrable bounded
  have normalizedBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) * ‖input elapsed‖) ≤
      (15 / 2 : ℝ) * seed := by
    convert bounded using 1 <;> dsimp only [seed, frozen] <;> rw [normalization.frozenDisplacement] <;> ring
  refine ⟨integrable, normalizedBound.trans ?_⟩
  have seedNonnegative : 0 ≤ seed := by dsimp only [seed]; positivity
  change (15 / 2 : ℝ) * seed ≤ 8 * seed
  nlinarith

end EulerNonuniqueness.Paper
