import EulerNonuniqueness.Section5.CascadeCoarserBlockCenterCoefficientReturn
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadeBlockCenterCoefficientContinuity
import EulerNonuniqueness.Section6.SourcePacketPairedBlockCenterCoefficientBudget
import EulerNonuniqueness.Section6.SourcePacketFinerBlockCenterCoefficientSeedTail
import EulerNonuniqueness.Section6.MovingForeignCoefficientSum
import EulerNonuniqueness.General.WeightedSeriesIntegralMajorant
import EulerNonuniqueness.General.ErasedAdjacentSum

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_driven_blockcenter_coefficient_weighted_return :
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
      first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun time => quadrupoleCenter first.patchMotion time receiver) receiverRadius (power + 1) (start + elapsed) -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun time => quadrupoleCenter second.patchMotion time receiver) receiverRadius (power + 1) (start + elapsed)
    let series := fun elapsed => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖
    (∀ power : ℕ, ContinuousOn (coefficient power) (Icc 0 horizon)) ∧
    (∀ elapsed ∈ Icc 0 horizon, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖)) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * series elapsed) volume 0 horizon ∧
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * series elapsed) ≤
        (coarserConstant / changed.location (receiver.val + 1) ^ 4) *
          (216360000 * changed.hessian + 576 * changed.strain) *
          (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
            ‖fun index : Fin count => if index.val ≤ receiver.val then
              changed.location (index.val + 1) ^ 4 * prepared.macroSourceState (start + elapsed) index else 0‖) +
        packetConstant * changed.seed (receiver.val + 1) + tolerance * changed.seed (receiver.val + 1) / decay := by
  obtain ⟨coarserCap, coarserPositive, coarserConstant, coarserNonnegative, coarserFactory⟩ :=
    exists_uniform_actual_coarser_block_center_coefficient_return
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  obtain ⟨radius, radiusPositive, radiusSmall, packetConstant, packetNonnegative, packetFactory⟩ :=
    exists_actual_paired_blockcenter_source_coefficient_seed_budget
  let rawCap := min coarserCap continuityCap
  have rawPositive : 0 < rawCap := lt_min coarserPositive continuityPositive
  refine ⟨rawCap, rawPositive, radius, radiusPositive, radiusSmall, coarserConstant, coarserNonnegative,
    packetConstant, packetNonnegative, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive ratioPower tolerance tolerancePositive referenceConstant
    referenceNonnegative amplitudeBound threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall
  have ratioBound : 2 ≤ scales.ratio := by linarith only [ratioLarge]
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [coarserFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall
      referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_actual_finer_blockcenter_coefficient_seed_tail amplitudePositive ratioBound alphaPositive ratioPower
      tolerancePositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_blockcenter_coefficient_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    packetFactory scales amplitudePositive ratioLarge alphaPositive referenceConstant referenceNonnegative amplitudeBound
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant radiusFactor initialError factorPositive
      factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall,
    eventually_gt_atTop (0 : ℝ)] with frequency coarser finer regularity packet frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prehistory receiverRadius receiverNonnegative receiverSmall
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let decay := 2 * Real.sqrt 2 * changed.omega source.val
  let sourceCoefficient := fun index power elapsed =>
    (first.quadrupoleSubfamily index).exteriorTaylorCoefficient Finset.univ
        (fun time => quadrupoleCenter first.patchMotion time receiver) receiverRadius (power + 1) (start + elapsed) -
      (second.quadrupoleSubfamily index).exteriorTaylorCoefficient Finset.univ
        (fun time => quadrupoleCenter second.patchMotion time receiver) receiverRadius (power + 1) (start + elapsed)
  let coefficient := fun power elapsed => first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
      (fun time => quadrupoleCenter first.patchMotion time receiver) receiverRadius (power + 1) (start + elapsed) -
    second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
      (fun time => quadrupoleCenter second.patchMotion time receiver) receiverRadius (power + 1) (start + elapsed)
  let sourceSeries := fun index elapsed => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖sourceCoefficient index power elapsed‖
  let series := fun elapsed => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖
  let maskedState := fun elapsed => ‖fun index : Fin count => if index.val ≤ receiver.val then
    changed.location (index.val + 1) ^ 4 * prepared.macroSourceState (start + elapsed) index else 0‖
  let coarserCoefficient := (coarserConstant / changed.location (receiver.val + 1) ^ 4) *
    (216360000 * changed.hessian + 576 * changed.strain)
  let remainder := tolerance * changed.seed (receiver.val + 1)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioLarge]
  have decayPositive : 0 < decay := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive source.val
    dsimp only [decay]
    positivity
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith only [startNonnegative, inside.1], by linarith only [inside.2, endBound]⟩
  have receiverRadiusSmall : receiverRadius ≤ changed.location (receiver.val + 1) / (100000 * 96) :=
    receiverSmall.trans (div_le_div_of_nonneg_right (changed.location_antitone (by omega)) (by norm_num))
  let enlarged := prepared.enlargeCap (min_le_left coarserCap continuityCap)
  have coarse (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      (∀ index ∈ Finset.univ.filter (fun index : Fin count => index.val < receiver.val),
        Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖sourceCoefficient index power elapsed‖)) ∧
      (∑ index ∈ Finset.univ.filter (fun index : Fin count => index.val < receiver.val), sourceSeries index elapsed) ≤
        coarserCoefficient * maskedState elapsed := by
    have actual := coarser count phase dipoleAngle enlarged path (timeRange elapsed inside) receiver
      receiverRadius receiverNonnegative receiverRadiusSmall
    with_reducible_and_instances
      dsimp only [sourceCoefficient, sourceSeries, coarserCoefficient, maskedState, changed, first, second,
        CascadeSourcePreparedPair.macroSourceState, enlarged, CascadeSourcePreparedPair.enlargeCap] at actual ⊢
      exact actual
  have fine (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      (∀ index : Fin count, receiver.val + 2 ≤ index.val →
        Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖sourceCoefficient index power elapsed‖)) ∧
      (∑ index ∈ Finset.univ.filter (fun index : Fin count => receiver.val + 2 ≤ index.val), sourceSeries index elapsed) ≤
        remainder := finer count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path (start + elapsed)
          (timeRange elapsed inside) receiver receiverRadius receiverNonnegative receiverRadiusSmall
  obtain ⟨adjacentContinuous, adjacentSummable, adjacentIntegrable, adjacentBound⟩ :=
    packet count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source adjacent start horizon
      initialDistance outgoingPhase startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall
      ratioBudget initialBudget firstInitial secondInitial initialProjection initialUpper prehistory
      receiverRadius receiverNonnegative receiverSmall
  have seedIdentity : Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * changed.location (source.val + 1) ^ 4) =
      changed.seed (receiver.val + 1) := by
    rw [Scales.seed, changed.adjacent_location_distance, ← adjacent]
  have adjacentBudget : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * sourceSeries source elapsed) ≤
      packetConstant * changed.seed (receiver.val + 1) := by
    change (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * sourceSeries source elapsed) ≤
      packetConstant * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * changed.location (source.val + 1) ^ 4)) at adjacentBound
    rw [seedIdentity] at adjacentBound
    exact adjacentBound
  have split (power : ℕ) (elapsed : ℝ) : coefficient power elapsed =
      ∑ index ∈ Finset.univ.erase receiver, sourceCoefficient index power elapsed := by
    dsimp only [coefficient, sourceCoefficient]
    rw [first.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles,
      second.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles, ← Finset.sum_sub_distrib]
  have coefficientContinuous (power : ℕ) : ContinuousOn (coefficient power) (Icc 0 horizon) :=
    ((regularity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver receiverRadius power).1).comp
      (continuousOn_const.add continuousOn_id) (fun elapsed inside => timeRange elapsed inside)
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power elapsed‖) ∧
      series elapsed ≤ coarserCoefficient * maskedState elapsed + sourceSeries source elapsed + remainder := by
    have allSummable (index : Fin count) (member : index ∈ Finset.univ.erase receiver) :
        Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖sourceCoefficient index power elapsed‖) := by
      by_cases below : index.val < receiver.val
      · exact (coarse elapsed inside).1 index (Finset.mem_filter.mpr ⟨Finset.mem_univ _, below⟩)
      by_cases same : index = source
      · subst index
        exact adjacentSummable elapsed inside
      exact (fine elapsed inside).1 index (by
        have different := (Finset.mem_erase.mp member).1
        have sourceDifferent : index.val ≠ source.val := fun identity => same (Fin.ext identity)
        have receiverDifferent : index.val ≠ receiver.val := fun identity => different (Fin.ext identity)
        omega)
    have assembled := General.summable_weighted_norm_of_eq_add_finite_corrections
      (Finset.univ.erase receiver) (fun power : ℕ => (96 : ℝ) ^ (power + 1))
      (fun _ => by positivity) (fun power => coefficient power elapsed) (fun _ => (0 : ℂ))
      (fun index power => sourceCoefficient index power elapsed)
      (fun power => by simpa only [zero_add] using split power elapsed)
      (by simp only [norm_zero, mul_zero]; exact summable_zero) allSummable
    have upper := assembled.2
    simp only [norm_zero, mul_zero, tsum_zero, zero_add] at upper
    rw [General.sum_erase_eq_lower_add_adjacent_add_finer receiver source adjacent] at upper
    exact ⟨assembled.1, upper.trans (add_le_add (add_le_add_right (coarse elapsed inside).2 _) (fine elapsed inside).2)⟩
  have maskedContinuous : ContinuousOn maskedState (Icc 0 horizon) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro index
    by_cases selected : index.val ≤ receiver.val
    · simp only [if_pos selected]
      exact continuousOn_const.mul (((stateContinuity prepared rawPositive (min_le_right _ _) path index).2.2.2).comp
        (continuousOn_const.add continuousOn_id) (fun elapsed inside => timeRange elapsed inside))
    · simp only [if_neg selected]
      exact continuousOn_const
  have exponentialContinuous : ContinuousOn (fun elapsed : ℝ => Real.exp (-decay * elapsed)) (Icc 0 horizon) := by fun_prop
  have maskedIntegrable := (exponentialContinuous.mul maskedContinuous).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have exponentialIntegrable := exponentialContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have majorantIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) *
      (coarserCoefficient * maskedState elapsed + sourceSeries source elapsed + remainder)) volume 0 horizon := by
    convert ((maskedIntegrable.const_mul coarserCoefficient).add adjacentIntegrable).add
      (exponentialIntegrable.const_mul remainder) using 1
    funext elapsed
    ring
  have integrated := General.intervalIntegrable_weighted_tsum_of_integrable_majorant horizonNonnegative
    (fun power => continuousOn_const.mul (coefficientContinuous power).norm)
    (fun _ _ _ => by positivity) (fun elapsed inside => (pointwise elapsed inside).1)
    exponentialContinuous (fun _ _ => (Real.exp_pos _).le) majorantIntegrable
    (fun elapsed inside => (pointwise elapsed inside).2)
  have integralIdentity : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      (coarserCoefficient * maskedState elapsed + sourceSeries source elapsed + remainder)) =
      coarserCoefficient * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * maskedState elapsed) +
        (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * sourceSeries source elapsed) +
        remainder * ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) := by
    simp_rw [mul_add, mul_left_comm (Real.exp _) coarserCoefficient, mul_comm (Real.exp _) remainder]
    rw [intervalIntegral.integral_add ((maskedIntegrable.const_mul _).add adjacentIntegrable)
        (exponentialIntegrable.const_mul _),
      intervalIntegral.integral_add (maskedIntegrable.const_mul _) adjacentIntegrable]
    simp only [intervalIntegral.integral_const_mul]
    rfl
  have exponentialBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed)) ≤ 1 / decay := by
    simpa only [zero_mul, zero_add, one_mul, mul_one, zero_div] using
      laplace_affine_integral_bound decayPositive (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) horizonNonnegative
  have remainderNonnegative : 0 ≤ remainder := mul_nonneg tolerancePositive.le
    (changed.seed_pos frequencyPositive ratioPositive _).le
  refine ⟨coefficientContinuous, fun elapsed inside => (pointwise elapsed inside).1, integrated.1, ?_⟩
  have bound := integrated.2.trans_eq integralIdentity
  have remainderBound := mul_le_mul_of_nonneg_left exponentialBound remainderNonnegative
  have finalBound := bound.trans (add_le_add (add_le_add_left adjacentBudget _) remainderBound)
  convert finalBound using 1 <;> dsimp only [coarserCoefficient, maskedState, remainder, decay, series] <;> ring

end EulerNonuniqueness.Paper
