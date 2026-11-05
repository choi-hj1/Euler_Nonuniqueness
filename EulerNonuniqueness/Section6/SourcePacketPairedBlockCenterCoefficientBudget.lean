import EulerNonuniqueness.Section6.SourcePacketActualBlockCenterCoefficientBudget
import EulerNonuniqueness.Section6.SourcePacketReferenceBlockCenterCoefficientWindow
import EulerNonuniqueness.General.WeightedPairSeriesIntegral

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 750000

theorem exists_actual_paired_blockcenter_source_coefficient_seed_budget :
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
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let distance := changed.location (source.val + 1)
    let decay := 2 * Real.sqrt 2 * changed.omega source.val
    let coefficient := fun power elapsed =>
      (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun time => quadrupoleCenter first.patchMotion time receiver) receiverRadius (power + 1) (start + elapsed) -
        (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun time => quadrupoleCenter second.patchMotion time receiver) receiverRadius (power + 1) (start + elapsed)
    let series := fun elapsed => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖
    (∀ power : ℕ, ContinuousOn (coefficient power) (Icc 0 horizon)) ∧
    (∀ elapsed ∈ Icc 0 horizon, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖)) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * series elapsed) volume 0 horizon ∧
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * series elapsed) ≤
        constant * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)) := by
  obtain ⟨radius, radiusPositive, radiusSmall, alternativeConstant, alternativeNonnegative, alternatives⟩ :=
    exists_actual_blockcenter_source_coefficient_seed_budget
  obtain ⟨referenceConstant, referenceNonnegative, references⟩ := exists_uniform_actual_reference_blockcenter_coefficient_window
  refine ⟨radius, radiusPositive, radiusSmall, alternativeConstant + referenceConstant,
    add_nonneg alternativeNonnegative referenceNonnegative, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive referenceBound referenceBoundNonnegative amplitudeBound threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant radiusFactor initialError factorPositive factorSmall rootOne boundaryOne
    radiusFactorPositive initialErrorSmall
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [alternatives scales amplitudePositive ratioLarge alphaPositive referenceBound referenceBoundNonnegative amplitudeBound
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant radiusFactor initialError factorPositive factorSmall
      rootOne boundaryOne radiusFactorPositive initialErrorSmall,
    references scales amplitudePositive ratioLarge alphaPositive orbit sectionTime thresholdSmall referenceBoundNonnegative
      rootOne boundaryOne factorPositive factorOne]
    with frequency alternatives references
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prehistory receiverRadius receiverNonnegative receiverSmall
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let decay := 2 * Real.sqrt 2 * changed.omega source.val
  let distance := changed.location (source.val + 1)
  let seed := Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)
  let firstCoefficient := fun power elapsed => (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
    (fun time => quadrupoleCenter first.patchMotion time receiver) receiverRadius (power + 1) (start + elapsed)
  let secondCoefficient := fun power elapsed => (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
    (fun time => quadrupoleCenter second.patchMotion time receiver) receiverRadius (power + 1) (start + elapsed)
  obtain ⟨firstContinuous, firstSummable, firstIntegrable, firstBound⟩ :=
    alternatives count phase dipoleAngle prepared path receiver source adjacent start horizon initialDistance outgoingPhase
      startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
      firstInitial secondInitial initialProjection initialUpper prehistory receiverRadius receiverNonnegative receiverSmall
  obtain ⟨secondContinuous, secondSummable, secondIntegrable, secondBound⟩ :=
    references count phase dipoleAngle prepared path receiver source adjacent start horizon receiverRadius
      startNonnegative horizonNonnegative endBound receiverNonnegative receiverSmall
  have exponentialContinuous : ContinuousOn (fun elapsed : ℝ => Real.exp (-decay * elapsed)) (Icc 0 horizon) := by fun_prop
  have paired := General.intervalIntegrable_weighted_pair_tsum_of_integrable_sides
    (first := firstCoefficient) (second := secondCoefficient) (sequenceWeight := fun power => (96 : ℝ) ^ (power + 1))
    (timeWeight := fun elapsed => Real.exp (-decay * elapsed)) horizonNonnegative firstContinuous secondContinuous
    (fun _ => by positivity) exponentialContinuous (fun _ _ => (Real.exp_pos _).le)
    firstSummable secondSummable firstIntegrable secondIntegrable
  have referenceCoefficientBound : referenceConstant / scales.ratio ≤ referenceConstant :=
    div_le_self referenceNonnegative (by linarith)
  have seedNonnegative : 0 ≤ seed := by dsimp only [seed]; positivity
  have referenceBound' := secondBound.trans (mul_le_mul_of_nonneg_right referenceCoefficientBound seedNonnegative)
  refine ⟨fun power => (firstContinuous power).sub (secondContinuous power), paired.1, paired.2.1, ?_⟩
  have bound := paired.2.2.trans (add_le_add firstBound referenceBound')
  convert bound using 1 <;> ring

end EulerNonuniqueness.Paper
