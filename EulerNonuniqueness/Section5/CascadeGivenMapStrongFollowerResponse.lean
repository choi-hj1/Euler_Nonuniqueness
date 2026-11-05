import EulerNonuniqueness.Section5.CascadeStrongFollowerEnvelopeVolterra
import EulerNonuniqueness.Section5.CascadeFiniteCoordinateChartComparison
import EulerNonuniqueness.Section5.CascadeSharpStateFiniteCoordinateBound
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_given_map_strong_follower_response
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
    ∃ comparisonConstant ≥ (1 : ℝ), ∃ feedbackConstant ≥ (0 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (2 * constant) ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ,
    threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ drive : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time receiver| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time receiver| ≤ radius) →
    ∃ lift : Fin count → Fin 2 → ℝ → ℝ,
      (∀ receiver side, Continuous (lift receiver side) ∧ lift receiver side 0 = phase (receiver.val + 1)) ∧
      (∀ receiver : Fin count, receiver.val < drive.val → ∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
            Complex.exp (Complex.I * (lift receiver side time : ℂ))) ∧
      let changed : Scales := {scales with frequency := frequency}
      let envelope := fun time => ‖fun receiver : Fin count => if receiver.val < drive.val then
        changed.location (receiver.val + 1) ^ 4 *
          (prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) else 0‖
      let remaining := prepared.followerRemainingForcing drive
      let rho := 216360000 * changed.hessian + 576 * changed.strain
      let rate := constant * changed.omega (drive.val + 1) / changed.ratio + constant * (feedbackConstant * rho)
      ContinuousOn envelope (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
      IntervalIntegrable envelope volume 0 finish ∧ IntervalIntegrable remaining volume 0 finish ∧
      envelope 0 = 0 ∧ ∀ time ∈ Icc 0 finish,
        IntervalIntegrable (fun current => Real.exp (rate * (time - current)) * remaining current) volume 0 time ∧
        envelope time ≤ (comparisonConstant * constant) * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * remaining current := by
  classical
  obtain ⟨baseGraph, baseCoordinate, baseGraphAnalytic, baseGraphZero, baseGraphDerivative,
    baseCoordinateSmooth, baseCoordinateZero, baseCoordinateDerivative, thresholdMax, thresholdPositive,
    thresholdEighth, baseCap, baseCapPositive, baseFactory⟩ :=
      exists_uniform_actual_strong_follower_envelope_volterra
  obtain ⟨comparisonRadius, comparisonPositive, comparisonQuarter, comparisonConstant, comparisonOne, comparison⟩ :=
    exists_uniform_actual_finite_coordinate_chart_comparison baseGraphAnalytic baseCoordinateSmooth
      baseGraphZero baseCoordinateZero baseGraphDerivative baseCoordinateDerivative graphAnalytic coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨outputRadius, outputPositive, _, _, _, outputFactory⟩ :=
    exists_uniform_actual_sharp_state_finite_coordinate_bound graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min baseCap continuityCap
  have rawPositive : 0 < rawCap := lt_min baseCapPositive continuityPositive
  have baseCapBound : rawCap ≤ baseCap := min_le_left _ _
  have continuityCapBound : rawCap ≤ continuityCap := min_le_right _ _
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨baseRadius, basePositive, baseQuarter, constant, constantOne, _, _, feedbackConstant,
    feedbackNonnegative, rootMin, rootEight, responses⟩ := baseFactory factorPositive factorSmall
  let radius := min baseRadius (min outputRadius (comparisonRadius / 2))
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusBase : radius ≤ baseRadius := min_le_left _ _
  have radiusOutput : radius ≤ outputRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusComparison : radius < comparisonRadius :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  refine ⟨radius, radiusPositive, radiusBase.trans baseQuarter, constant, constantOne,
    comparisonConstant, comparisonOne, feedbackConstant, feedbackNonnegative, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne orbit sectionTime
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [responses scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant
      boundaryConstant thresholdBound referenceNonnegative boundaryOne orbit sectionTime,
    outputFactory scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive (factorSmall.trans (by norm_num)) thresholdSmall referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative comparisonPositive]
    with frequency baseResponse outputGeometry referenceSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path drive finish finishNonnegative finishBound small
  let changed : Scales := {scales with frequency := frequency}
  have rawCapInvariant : (prepared.enlargeCap baseCapBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have sizeCapInvariant (chosenGraph chosenCoordinate : ℝ → ℝ) (chosen : Fin 2 → ℝ → ℝ) :
      (prepared.enlargeCap baseCapBound).finiteCoordinateSize chosenGraph chosenCoordinate chosen =
        prepared.finiteCoordinateSize chosenGraph chosenCoordinate chosen := rfl
  have remainingCapInvariant : (prepared.enlargeCap baseCapBound).followerRemainingForcing =
      prepared.followerRemainingForcing := rfl
  obtain ⟨lift, liftProperties, liftPolar, data⟩ := baseResponse count phase dipoleAngle
    (prepared.enlargeCap baseCapBound) path drive finish finishNonnegative finishBound
      (fun receiver below time inside => (small receiver below time inside).trans radiusBase)
  dsimp only at data
  simp only [sizeCapInvariant, rawCapInvariant, remainingCapInvariant] at data
  obtain ⟨baseContinuous, remainingContinuous, _, remainingIntegrable, baseInitial, _, resolved⟩ := data
  let raw := fun receiver time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
  let state := fun chosenGraph chosenCoordinate receiver time => changed.location (receiver.val + 1) ^ 4 *
    (prepared.finiteCoordinateSize chosenGraph chosenCoordinate (lift receiver) receiver time + raw receiver time)
  let baseEnvelope := fun time => ‖fun receiver : Fin count => if receiver.val < drive.val then
    state baseGraph baseCoordinate receiver time else 0‖
  let envelope := fun time => ‖fun receiver : Fin count => if receiver.val < drive.val then
    state graph coordinate receiver time else 0‖
  let remaining := prepared.followerRemainingForcing drive
  let rate := constant * changed.omega (drive.val + 1) / changed.ratio +
    constant * (feedbackConstant * (216360000 * changed.hessian + 576 * changed.strain))
  have prefixSubset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have rawContinuous (receiver : Fin count) : ContinuousOn (raw receiver) (Icc 0 finish) :=
    continuousOn_finset_sum _ (fun patch _ =>
      ((stateContinuity prepared rawPositive continuityCapBound path receiver).1 patch).mono prefixSubset)
  have outputContinuous (receiver : Fin count) (below : receiver.val < drive.val) :
      ContinuousOn (prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver) (Icc 0 finish) := by
    have nonterminal : receiver.val + 1 < count := by omega
    exact (outputGeometry prepared path receiver nonterminal finish finishNonnegative finishBound
      (fun time inside => (small receiver below time inside).trans radiusOutput) (lift receiver)
      (fun side => (liftProperties receiver side).1.continuousOn)
      (fun side => (liftProperties receiver side).2) (liftPolar receiver below)).1
  have envelopeContinuous : ContinuousOn envelope (Icc 0 finish) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro receiver
    by_cases below : receiver.val < drive.val
    · simpa only [below, ite_true] using
        (continuousOn_const.mul ((outputContinuous receiver below).add (rawContinuous receiver)) :
          ContinuousOn (state graph coordinate receiver) (Icc 0 finish))
    · simpa only [below, ite_false] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 finish))
  have rawNonnegative (receiver : Fin count) (time : ℝ) : 0 ≤ raw receiver time := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have stateNonnegative (chosenGraph chosenCoordinate : ℝ → ℝ) (receiver : Fin count) (time : ℝ) :
      0 ≤ state chosenGraph chosenCoordinate receiver time := by
    have locationPositive := changed.location_pos (receiver.val + 1)
    have sizeNonnegative : 0 ≤ prepared.finiteCoordinateSize chosenGraph chosenCoordinate (lift receiver) receiver time := by
      dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize]
      positivity
    exact mul_nonneg (pow_nonneg locationPositive.le 4) (add_nonneg sizeNonnegative (rawNonnegative receiver time))
  have envelopeComparison (time : ℝ) (inside : time ∈ Icc 0 finish) :
      envelope time ≤ comparisonConstant * baseEnvelope time := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (zero_le_one.trans comparisonOne) (norm_nonneg _))).mpr
    intro receiver
    by_cases below : receiver.val < drive.val
    · have referenceChart := referenceSmall prepared.toCascadeMaterialPreparedPair time
        ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩ receiver
      have referenceInside : |unstableShape prepared.reference time receiver| +
          |stableShape prepared.reference time receiver| < comparisonRadius := by
        linarith [abs_nonneg (diagonalDifference prepared.reference time receiver /
          changed.length (receiver.val + 1) ^ 2 - 1)]
      have coordinateBound := (comparison prepared (lift receiver) receiver time
        ((small receiver below time inside).trans_lt radiusComparison) referenceInside).2
      have scaled := mul_le_mul_of_nonneg_left coordinateBound
        (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
      have stateBound : state graph coordinate receiver time ≤
          comparisonConstant * state baseGraph baseCoordinate receiver time := by
        convert scaled using 1; dsimp only [state, raw]; ring
      have component := norm_le_pi_norm (fun current : Fin count => if current.val < drive.val then
        state baseGraph baseCoordinate current time else 0) receiver
      simp only [below, ite_true, Real.norm_eq_abs,
        abs_of_nonneg (stateNonnegative baseGraph baseCoordinate receiver time)] at component
      have bound := stateBound.trans (mul_le_mul_of_nonneg_left component (zero_le_one.trans comparisonOne))
      simpa only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg (stateNonnegative graph coordinate receiver time)] using bound
    · simp only [below, ite_false, norm_zero]
      exact mul_nonneg (zero_le_one.trans comparisonOne) (norm_nonneg _)
  have initial : envelope 0 = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    have bound := envelopeComparison 0 ⟨le_rfl, finishNonnegative⟩
    have zero : baseEnvelope 0 = 0 := baseInitial
    simpa only [zero, mul_zero] using bound
  refine ⟨lift, liftProperties, liftPolar, envelopeContinuous, remainingContinuous,
    envelopeContinuous.intervalIntegrable_of_Icc finishNonnegative, remainingIntegrable, initial, ?_⟩
  intro time inside
  have kernelIntegrable : IntervalIntegrable (fun current => Real.exp (rate * (time - current)) * remaining current)
      volume 0 time := (resolved time inside).2.1
  have baseBound : baseEnvelope time ≤ constant * ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * remaining current := (resolved time inside).2.2.2
  refine ⟨kernelIntegrable, (envelopeComparison time inside).trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left baseBound (zero_le_one.trans comparisonOne)

end EulerNonuniqueness.Paper
