import EulerNonuniqueness.Section5.CascadeDrivenBlockCenterCoefficientWeightedReturn

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_driven_blockcenter_unweighted_return :
    ∃ rawCap > (0 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∃ coarserConstant ≥ (0 : ℝ), ∃ packetConstant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 8192 ≤ scales.ratio → 0 < scales.alpha →
    4 < scales.ratio ^ scales.alpha → ∀ tolerance > (0 : ℝ),
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant radiusFactor initialError : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant → 0 < radiusFactor → initialError ≤ 1 / 64 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start horizon initialDistance outgoingPhase : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    2048 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    12 * initialDistance ≤ scales.ratio → 20 * initialError + 83200 / initialDistance ^ 2 ≤ 1 / 5120 →
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
    let decay := 2 * Real.sqrt 2 * changed.omega source.val
    let coefficient := fun power elapsed =>
      quadrupoleExteriorCoefficient changed first.patchMotion receiver (start + elapsed) receiverRadius power -
        quadrupoleExteriorCoefficient changed second.patchMotion receiver (start + elapsed) receiverRadius power
    let series := fun elapsed => ∑' power : ℕ, ‖coefficient power elapsed‖
    (∀ power : ℕ, ContinuousOn (coefficient power) (Icc 0 horizon)) ∧
    (∀ elapsed ∈ Icc 0 horizon, Summable (fun power : ℕ => ‖coefficient power elapsed‖)) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * series elapsed) volume 0 horizon ∧
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * series elapsed) ≤
        (coarserConstant / changed.location (receiver.val + 1) ^ 4) *
          (216360000 * changed.hessian + 576 * changed.strain) *
          (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
            ‖fun index : Fin count => if index.val ≤ receiver.val then
              changed.location (index.val + 1) ^ 4 * prepared.macroSourceState (start + elapsed) index else 0‖) +
        packetConstant * changed.seed (receiver.val + 1) + tolerance * changed.seed (receiver.val + 1) / decay := by
  obtain ⟨rawCap, capPositive, radius, radiusPositive, radiusSmall, coarserConstant, coarserNonnegative,
    packetConstant, packetNonnegative, driverFactory⟩ := exists_uniform_actual_driven_blockcenter_coefficient_weighted_return
  refine ⟨rawCap, capPositive, radius, radiusPositive, radiusSmall, coarserConstant, coarserNonnegative,
    packetConstant, packetNonnegative, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive ratioPower tolerance tolerancePositive referenceConstant
    referenceNonnegative amplitudeBound threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall
  have ratioBound : 2 ≤ scales.ratio := by linarith only [ratioLarge]
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  filter_upwards [driverFactory scales amplitudePositive ratioLarge alphaPositive ratioPower tolerance tolerancePositive
      referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
      radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num))]
    with frequency driver clearance
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prehistory receiverRadius receiverNonnegative receiverSmall
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let decay := 2 * Real.sqrt 2 * changed.omega source.val
  let materialCoefficient := fun power elapsed => first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
      (fun current => quadrupoleCenter first.patchMotion current receiver) receiverRadius (power + 1) (start + elapsed) -
    second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
      (fun current => quadrupoleCenter second.patchMotion current receiver) receiverRadius (power + 1) (start + elapsed)
  let coefficient := fun power elapsed =>
    quadrupoleExteriorCoefficient changed first.patchMotion receiver (start + elapsed) receiverRadius power -
      quadrupoleExteriorCoefficient changed second.patchMotion receiver (start + elapsed) receiverRadius power
  let materialSeries := fun elapsed => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖materialCoefficient power elapsed‖
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith only [startNonnegative, inside.1], by linarith only [inside.2, endBound]⟩
  obtain ⟨materialContinuous, materialSummable, materialIntegrable, materialBound⟩ :=
    driver count phase dipoleAngle prepared path receiver source adjacent start horizon initialDistance outgoingPhase
      startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
      firstInitial secondInitial initialProjection initialUpper prehistory receiverRadius receiverNonnegative receiverSmall
  have oneSide (family : FiniteMovingPatchFamily (count * 4))
      (densities : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4)
      (time : ℝ) (separated : ∀ sender ∈ Finset.univ.erase receiver, ∀ patch position,
        position ∈ family.patchMotion.domain time sender patch →
          |changed.location (receiver.val + 1) - changed.location (sender.val + 1)| / 8 ≤
            ‖quadrupoleCenter family.patchMotion time receiver - position‖) (power : ℕ) :
      family.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => quadrupoleCenter family.patchMotion current receiver) receiverRadius (power + 1) time =
        quadrupoleExteriorCoefficient changed family.patchMotion receiver time receiverRadius power := by
    let distance := changed.location (receiver.val + 1) / 1000
    have distancePositive : 0 < distance := div_pos (changed.location_pos _) (by norm_num)
    apply family.exteriorTaylorCoefficient_foreign_eq_quadrupoleExteriorCoefficient changed densities receiver receiverRadius time power distancePositive
    intro sender member patch position positionMember
    have actual := separated sender member patch position positionMember
    have spacing := changed.location_sum_le_three_distance (show receiver.val + 1 ≠ sender.val + 1 by
      intro identity
      exact (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel identity)).symm)
    dsimp only [distance]
    linarith only [actual, spacing, changed.location_pos (receiver.val + 1), changed.location_pos (sender.val + 1)]
  have coefficientIdentity (power : ℕ) (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      materialCoefficient power elapsed = coefficient power elapsed := by
    have clear := clearance count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path (start + elapsed) (timeRange elapsed inside) receiver
    dsimp only [materialCoefficient, coefficient]
    rw [oneSide first prepared.densityIdentity (start + elapsed) clear.2 power,
      oneSide second prepared.referenceWitness.densityIdentity (start + elapsed) clear.1 power]
  have coefficientContinuous (power : ℕ) : ContinuousOn (coefficient power) (Icc 0 horizon) :=
    (materialContinuous power).congr (fun elapsed inside => (coefficientIdentity power elapsed inside).symm)
  have weightedSummable (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖) := by
    exact (materialSummable elapsed inside).congr (fun power =>
      congrArg (fun value : ℂ => (96 : ℝ) ^ (power + 1) * ‖value‖) (coefficientIdentity power elapsed inside))
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      Summable (fun power : ℕ => ‖coefficient power elapsed‖) ∧
        (∑' power : ℕ, ‖coefficient power elapsed‖) ≤ materialSeries elapsed := by
    have dominates (power : ℕ) : ‖coefficient power elapsed‖ ≤ (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖ :=
      le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num))
    have summable := Summable.of_nonneg_of_le (fun power => norm_nonneg _) dominates (weightedSummable elapsed inside)
    have bound := summable.tsum_le_tsum dominates (weightedSummable elapsed inside)
    have identity : (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖) = materialSeries elapsed := by
      apply tsum_congr
      intro power
      exact congrArg (fun value : ℂ => (96 : ℝ) ^ (power + 1) * ‖value‖) (coefficientIdentity power elapsed inside).symm
    exact ⟨summable, bound.trans_eq identity⟩
  have exponentialContinuous : ContinuousOn (fun elapsed : ℝ => Real.exp (-decay * elapsed)) (Icc 0 horizon) := by fun_prop
  have integrated := General.intervalIntegrable_weighted_tsum_of_integrable_majorant
    (terms := fun power elapsed => ‖coefficient power elapsed‖)
    (weight := fun elapsed => Real.exp (-decay * elapsed)) (majorant := materialSeries)
    horizonNonnegative (fun power => (coefficientContinuous power).norm) (fun _ _ _ => norm_nonneg _)
    (fun elapsed inside => (pointwise elapsed inside).1) exponentialContinuous (fun _ _ => (Real.exp_pos _).le)
    materialIntegrable (fun elapsed inside => (pointwise elapsed inside).2)
  exact ⟨coefficientContinuous, fun elapsed inside => (pointwise elapsed inside).1, integrated.1,
    integrated.2.trans materialBound⟩

end EulerNonuniqueness.Paper
