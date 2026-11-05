import EulerNonuniqueness.Section5.CascadeGivenMapPairedPointRemainder
import EulerNonuniqueness.Section4.PaperShapeContinuity
import EulerNonuniqueness.General.PairedSaddleRemainderProfileIntegral
import EulerNonuniqueness.Section1.UniformIntegratedReferenceIndexBudget
import EulerNonuniqueness.Section5.Delay

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_uniform_actual_given_map_point_remainder_weighted_small
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ chartConstant ≥ (1 : ℝ), ∃ constant ≥ (1 : ℝ),
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ shapeMagnitude stateMagnitude tolerance : ℝ,
    0 ≤ shapeMagnitude → 0 ≤ stateMagnitude → 0 < tolerance →
    ∃ endpoint > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → 0 < factor → factor ≤ 1 / 8 →
    threshold ≤ thresholdMax → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∀ origin : ℝ,
    let changed : Scales := {scales with frequency := frequency}
    let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    let relative := fun time =>
      referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
        referenceStraightenedShape prepared.reference graph coordinate index time
    let shape := fun time => |(relative time).1| + |(relative time).2|
    let dilation := fun time => |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index -
      diagonalDifference prepared.reference time index| / changed.length (index.val + 1) ^ 2
    let remainder := relativeStraightenedSaddlePointRemainder changed (cascadePairedMotion prepared) graph coordinate index
    (∀ time ∈ Icc 0 finish, shape time ≤ shapeMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) →
    (∀ time ∈ Icc 0 finish, dilation time ≤ stateMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) →
    changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ≤ endpoint →
    ContinuousOn remainder (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-growth * time) * ‖remainder time‖) volume 0 finish ∧
    Real.exp (growth * origin) * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * ‖remainder time‖) ≤
      tolerance * changed.seed (index.val + 1) := by
  obtain ⟨chartConstant, chartOne, constant, constantOne, thresholdMax, thresholdPositive, thresholdEighth,
    pointRadius, pointPositive, pointQuarter, points⟩ :=
    exists_uniform_actual_given_map_paired_point_remainder graphSmooth coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  have chartRegular := localNormalFormChart_regular graphSmooth coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  have nearby := (chartRegular.1.eventually (by norm_num)).and
    ((localNormalFormError_contDiffAt_one graphSmooth coordinateSmooth 1).eventually (by norm_num))
  obtain ⟨regularRadius, regularPositive, regular⟩ := Metric.mem_nhds_iff.mp nearby
  let radius := min pointRadius (regularRadius / 2)
  have radiusPositive : 0 < radius := lt_min pointPositive (half_pos regularPositive)
  have radiusQuarter : radius ≤ 1 / 4 := (min_le_left _ _).trans pointQuarter
  refine ⟨chartConstant, chartOne, constant, constantOne, thresholdMax, thresholdPositive, thresholdEighth,
    radius, radiusPositive, radiusQuarter, ?_⟩
  intro shapeMagnitude stateMagnitude tolerance shapeNonnegative stateNonnegative tolerancePositive
  let endpoint := tolerance / (4 * constant * (1 + shapeMagnitude * (shapeMagnitude + stateMagnitude)))
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantOne
  have endpointPositive : 0 < endpoint := by dsimp only [endpoint]; positivity
  refine ⟨endpoint, endpointPositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdBound referenceNonnegative
  let referenceTolerance := tolerance / (4 * constant * (1 + shapeMagnitude + stateMagnitude))
  have referenceTolerancePositive : 0 < referenceTolerance := by dsimp only [referenceTolerance]; positivity
  filter_upwards [points scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive factorSmall
      thresholdBound referenceNonnegative,
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative radiusPositive,
    scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive
      (mul_nonneg (zero_le_one.trans chartOne) referenceNonnegative) referenceTolerancePositive,
    eventually_ge_atTop (1 : ℝ)] with frequency pointEstimate joint referenceSmall referenceRate frequencyOne
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small origin
  dsimp only
  intro shapeProfile stateProfile exposure
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let length := changed.length (index.val + 1)
  let motions := cascadePairedMotion prepared
  let raw := fun side time => (unstableShape (motions side) time index, stableShape (motions side) time index)
  let charts := fun side time => referenceStraightenedShape (motions side) graph coordinate index time
  let errors := fun side time => localNormalFormError 1 graph coordinate (raw side time)
  let diagonals := fun side time => diagonalDifference (motions side) time index / length ^ 2
  let shape := fun time => |(charts 0 time - charts 1 time).1| + |(charts 0 time - charts 1 time).2|
  let dilation := fun time => |diagonalDifference (motions 0) time index - diagonalDifference (motions 1) time index| / length ^ 2
  let remainder := relativeStraightenedSaddlePointRemainder changed motions graph coordinate index
  let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |(raw side time).1| + |(raw side time).2| ≤ radius := by
    fin_cases side
    · exact small time inside
    · have actual := referenceSmall prepared time ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩ index
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| ≤ radius
      linarith only [actual, abs_nonneg (diagonalDifference prepared.reference time index / length ^ 2 - 1)]
  have centroids (side : Fin 2) (patch : Fin 4) :
      Continuous (fun time => patchCentroid (motions side) time index patch) := by
    fin_cases side
    · exact prepared.trajectory.movingFamily.patchCentroid_continuous index patch
    · simpa only [motions, cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] using
        prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous index patch
  have rawContinuous (side : Fin 2) : ContinuousOn (raw side) (Icc 0 finish) :=
    paper_shape_continuousOn_of_centroids (motions side) index
      (fun patch => (centroids side patch).continuousOn)
      (fun time inside => (pairedSmall side time inside).trans radiusQuarter)
  have localInside (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      raw side time ∈ Metric.ball (0 : ℝ × ℝ) regularRadius := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    have bound := (pairedSmall side time inside).trans (min_le_right pointRadius (regularRadius / 2))
    apply max_lt <;> linarith only [bound, regularPositive, abs_nonneg (raw side time).1, abs_nonneg (raw side time).2]
  have chartContinuous (side : Fin 2) : ContinuousOn (charts side) (Icc 0 finish) := by
    intro time inside
    exact (regular (localInside side time inside)).1.continuousAt.comp_continuousWithinAt (rawContinuous side time inside)
  have errorContinuous (side : Fin 2) : ContinuousOn (errors side) (Icc 0 finish) := by
    intro time inside
    exact (regular (localInside side time inside)).2.continuousAt.comp_continuousWithinAt (rawContinuous side time inside)
  have diagonalContinuous (side : Fin 2) : Continuous (fun time => diagonalDifference (motions side) time index) := by
    exact ((((centroids side 0).sub (centroids side 1)).div_const 2).norm.pow 2).sub
      ((((centroids side 2).sub (centroids side 3)).div_const 2).norm.pow 2)
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) :=
    (((diagonalContinuous 0).sub (diagonalContinuous 1)).abs.div_const (length ^ 2)).continuousOn
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) :=
    ((chartContinuous 0).sub (chartContinuous 1)).fst.abs.add ((chartContinuous 0).sub (chartContinuous 1)).snd.abs
  have radialSmall (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans ((small time inside).trans (radiusQuarter.trans (by norm_num)))
  have diagonalNonzero (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) : diagonals side time ≠ 0 := by
    have lower : (1 / 2 : ℝ) ≤ diagonals side time := by
      fin_cases side
      · have actual := joint prepared path (thresholdBound.trans (thresholdEighth.trans (by norm_num))) factorSmall
          index nonterminal finish finishNonnegative finishBound radialSmall time inside
        have bound := (abs_le.mp actual.1).1
        change -(1 / 4 : ℝ) ≤ diagonals 0 time - 1 at bound
        change (1 / 2 : ℝ) ≤ diagonals 0 time
        linarith only [bound]
      · obtain ⟨_, _, _, _, _, coarse, _⟩ := prepared.referenceSolution
        exact (coarse.2.1 time ⟨inside.1, (inside.2.trans (finishBound.trans path.stopBound)).trans (by norm_num : (1 : ℝ) ≤ 2)⟩ index).2.2.1
    linarith only [lower]
  have frequencyContinuous (side : Fin 2) :
      ContinuousOn (fun time => omega / diagonals side time) (Icc 0 finish) :=
    continuousOn_const.div ((diagonalContinuous side).div_const (length ^ 2)).continuousOn (diagonalNonzero side)
  have dilationErrorContinuous : ContinuousOn (fun time =>
      dilationFrequencySaddleError omega (diagonals 0 time) (diagonals 1 time) (charts 0 time) (charts 1 time)) (Icc 0 finish) := by
    dsimp only [dilationFrequencySaddleError]
    have first : ContinuousOn (fun time => omega / diagonals 0 time - omega) (Icc 0 finish) :=
      (frequencyContinuous 0).sub continuousOn_const
    have second : ContinuousOn (fun time => omega / diagonals 1 time - omega) (Icc 0 finish) :=
      (frequencyContinuous 1).sub continuousOn_const
    exact (continuousOn_const.mul ((first.mul (chartContinuous 0).fst).sub (second.mul (chartContinuous 1).fst))).prodMk
      (continuousOn_const.mul ((first.mul (chartContinuous 0).snd).sub (second.mul (chartContinuous 1).snd)))
  have remainderContinuous : ContinuousOn remainder (Icc 0 finish) :=
    (dilationErrorContinuous.add ((frequencyContinuous 0).smul ((errorContinuous 0).sub (errorContinuous 1)))).add
      (((frequencyContinuous 0).sub (frequencyContinuous 1)).smul (errorContinuous 1))
  have exponential : Continuous (fun time : ℝ => Real.exp (-growth * time)) := by fun_prop
  have remainderI := (exponential.continuousOn.mul remainderContinuous.norm).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaGrowth : omega ≤ growth := by
    have lower : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    dsimp only [growth]
    nlinarith only [omegaPositive, lower]
  have growthPositive : 0 < growth := omegaPositive.trans_le omegaGrowth
  have seedPositive : 0 < changed.seed (index.val + 1) := changed.seed_pos frequencyPositive ratioPositive _
  have rateData := referenceRate (index.val + 1)
  have referenceNonnegative' : 0 ≤ referenceSize := by
    have actual := rateData.1
    change 0 ≤ omega * referenceSize at actual
    exact nonneg_of_mul_nonneg_right actual omegaPositive
  have pointBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      ‖remainder time‖ ≤ constant * omega * ((shape time + dilation time + referenceSize) * shape time +
        referenceSize * dilation time) + 0 := by
    have actual := pointEstimate prepared path index nonterminal finish finishNonnegative finishBound
      (fun time inside => (small time inside).trans (min_le_left _ _)) time inside
    change ‖remainder time‖ ≤ constant * |omega| * ((shape time + dilation time + referenceSize) * shape time +
      referenceSize * dilation time) at actual
    simpa only [abs_of_pos omegaPositive, add_zero] using actual
  have integrated := General.weighted_paired_saddle_remainder_le_of_profiles finishNonnegative growthPositive omegaPositive.le omegaGrowth
    shapeNonnegative stateNonnegative seedPositive referenceNonnegative' (zero_le_one.trans constantOne)
    shapeContinuous dilationContinuous remainderContinuous.norm (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 finish))
    (fun time _ => by dsimp only [shape]; positivity)
    (fun time _ => div_nonneg (abs_nonneg _) (sq_nonneg _))
    shapeProfile stateProfile pointBound exposure
  simp only [mul_zero, intervalIntegral.integral_zero, add_zero] at integrated
  have quadraticBound : constant * (shapeMagnitude * (shapeMagnitude + stateMagnitude) * endpoint) ≤ tolerance / 4 := by
    have comparison := mul_le_mul_of_nonneg_right
      (show shapeMagnitude * (shapeMagnitude + stateMagnitude) ≤ 1 + shapeMagnitude * (shapeMagnitude + stateMagnitude) by linarith)
      (mul_nonneg (zero_le_one.trans constantOne) endpointPositive.le)
    have identity : constant * (1 + shapeMagnitude * (shapeMagnitude + stateMagnitude)) * endpoint = tolerance / 4 := by
      dsimp only [endpoint]
      field_simp
      ring
    nlinarith only [comparison, identity]
  have referenceBound : constant * (omega * referenceSize * (shapeMagnitude + stateMagnitude) * finish) ≤ tolerance / 4 := by
    have first := mul_le_mul_of_nonneg_right
      (show omega * referenceSize ≤ referenceTolerance from rateData.2.le) (add_nonneg shapeNonnegative stateNonnegative)
    have second := mul_le_mul_of_nonneg_right first finishNonnegative
    have third := mul_le_mul_of_nonneg_left second (zero_le_one.trans constantOne)
    have finishOne : finish ≤ 1 := finishBound.trans path.stopBound
    have enlarged := mul_le_mul_of_nonneg_left finishOne
      (mul_nonneg (mul_nonneg (zero_le_one.trans constantOne) referenceTolerancePositive.le) (add_nonneg shapeNonnegative stateNonnegative))
    have slack : 0 ≤ constant * referenceTolerance := mul_nonneg (zero_le_one.trans constantOne) referenceTolerancePositive.le
    have identity : constant * referenceTolerance * (1 + shapeMagnitude + stateMagnitude) = tolerance / 4 := by
      dsimp only [referenceTolerance]
      field_simp
      ring
    nlinarith only [third, enlarged, slack, identity]
  refine ⟨remainderContinuous, remainderI, integrated.trans ?_⟩
  have scalar : constant * (shapeMagnitude * (shapeMagnitude + stateMagnitude) * endpoint +
      omega * referenceSize * (shapeMagnitude + stateMagnitude) * finish) ≤ tolerance := by
    nlinarith only [quadraticBound, referenceBound, tolerancePositive]
  exact mul_le_mul_of_nonneg_right scalar seedPositive.le

end EulerNonuniqueness.Paper

