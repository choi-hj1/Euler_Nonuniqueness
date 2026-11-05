import EulerNonuniqueness.Section5.CascadeCorrectedPhaseLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeCorrectedPhaseWeightedFeedback
import EulerNonuniqueness.Section5.CascadeFirstMomentLocalForeignArbitraryWeightReturn
import EulerNonuniqueness.Section5.CascadeForeignPatchCoefficientIntegrability
import EulerNonuniqueness.Section6.NormalFormInverseMatching
import EulerNonuniqueness.Section6.PaperCorrectedPhaseContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem phase_chart_tolerance_arbitrary_weight
    {tolerance pointTolerance chart moment center unstable shape : ℝ}
    (pointNonnegative : 0 ≤ pointTolerance) (pointBound : pointTolerance ≤ tolerance)
    (chartBound : pointTolerance * chart ≤ tolerance)
    (momentNonnegative : 0 ≤ moment) (centerNonnegative : 0 ≤ center) (shapeNonnegative : 0 ≤ shape)
    (unstableBound : unstable ≤ chart * shape) :
    pointTolerance * (moment + center + unstable) ≤ tolerance * (moment + center + shape) := by
  have first := mul_le_mul_of_nonneg_right pointBound (add_nonneg momentNonnegative centerNonnegative)
  have second := mul_le_mul_of_nonneg_left unstableBound pointNonnegative
  have third := mul_le_mul_of_nonneg_right chartBound shapeNonnegative
  nlinarith only [first, second, third]

private theorem weighted_phase_forcing_local_foreign_arbitrary_weight
    {moment center shape raw difference forcing : ℝ → ℝ} {foreign : Fin 4 → ℝ → ℝ}
    {finish weight tolerance constant omega epsilon : ℝ}
    (ordered : 0 ≤ finish)
    (momentIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * moment time) volume 0 finish)
    (centerIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * center time) volume 0 finish)
    (shapeIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * shape time) volume 0 finish)
    (rawIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * raw time) volume 0 finish)
    (differenceIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish)
    (foreignIntegrable : ∀ patch, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish)
    (forcingIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 finish)
    (pointwise : ∀ time ∈ Icc 0 finish,
      forcing time ≤ tolerance * (moment time + center time + shape time) +
        constant * omega * epsilon * (center time + raw time) +
        constant * difference time + constant * epsilon * ∑ patch, foreign patch time) :
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time) ≤
      tolerance * ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * moment time) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * shape time)) +
      constant * omega * epsilon * ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw time)) +
      constant * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
      constant * epsilon * ∑ patch, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time := by
  have foreignSumIntegrable : IntervalIntegrable
      (fun time => Real.exp (-weight * time) * ∑ patch, foreign patch time) volume 0 finish := by
    simp_rw [Finset.mul_sum]
    simpa only [Finset.sum_apply] using
      (IntervalIntegrable.sum Finset.univ (f := fun (patch : Fin 4) (time : ℝ) =>
        Real.exp (-weight * time) * foreign patch time) (fun patch _ => foreignIntegrable patch))
  have upperIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) *
      (tolerance * (moment time + center time + shape time) +
        constant * omega * epsilon * (center time + raw time) +
        constant * difference time + constant * epsilon * ∑ patch, foreign patch time)) volume 0 finish := by
    convert (((((momentIntegrable.add centerIntegrable).add shapeIntegrable).const_mul tolerance).add
      ((centerIntegrable.add rawIntegrable).const_mul (constant * omega * epsilon))).add
      (differenceIntegrable.const_mul constant)).add (foreignSumIntegrable.const_mul (constant * epsilon)) using 1
    ext time
    ring
  have comparison := intervalIntegral.integral_mono_on (μ := volume) ordered forcingIntegrable upperIntegrable
    (fun time inside => mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
  have identity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (tolerance * (moment time + center time + shape time) +
        constant * omega * epsilon * (center time + raw time) +
        constant * difference time + constant * epsilon * ∑ patch, foreign patch time)) =
      tolerance * ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * moment time) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * shape time)) +
      constant * omega * epsilon * ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw time)) +
      constant * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
      constant * epsilon * ∑ patch, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time := by
    have integrandIdentity (time : ℝ) : Real.exp (-weight * time) *
        (tolerance * (moment time + center time + shape time) +
          constant * omega * epsilon * (center time + raw time) +
          constant * difference time + constant * epsilon * ∑ patch, foreign patch time) =
        tolerance * ((Real.exp (-weight * time) * moment time + Real.exp (-weight * time) * center time) +
          Real.exp (-weight * time) * shape time) +
        constant * omega * epsilon * (Real.exp (-weight * time) * center time + Real.exp (-weight * time) * raw time) +
        constant * (Real.exp (-weight * time) * difference time) +
        constant * epsilon * (Real.exp (-weight * time) * ∑ patch, foreign patch time) := by ring
    simp_rw [integrandIdentity]
    rw [intervalIntegral.integral_add
        (((((momentIntegrable.add centerIntegrable).add shapeIntegrable).const_mul tolerance).add
          ((centerIntegrable.add rawIntegrable).const_mul (constant * omega * epsilon))).add
          (differenceIntegrable.const_mul constant)) (foreignSumIntegrable.const_mul (constant * epsilon)),
      intervalIntegral.integral_add
        ((((momentIntegrable.add centerIntegrable).add shapeIntegrable).const_mul tolerance).add
          ((centerIntegrable.add rawIntegrable).const_mul (constant * omega * epsilon)))
        (differenceIntegrable.const_mul constant),
      intervalIntegral.integral_add
        (((momentIntegrable.add centerIntegrable).add shapeIntegrable).const_mul tolerance)
        ((centerIntegrable.add rawIntegrable).const_mul (constant * omega * epsilon))]
    simp only [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add (momentIntegrable.add centerIntegrable) shapeIntegrable,
      intervalIntegral.integral_add momentIntegrable centerIntegrable,
      intervalIntegral.integral_add centerIntegrable rawIntegrable]
    congr 2
    simp_rw [Finset.mul_sum]
    exact intervalIntegral.integral_finset_sum (fun patch _ => foreignIntegrable patch)
  exact comparison.trans_eq identity

theorem exists_uniform_actual_cascade_corrected_phase_local_foreign_arbitrary_weight_return
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 8 → ∃ constant ≥ (0 : ℝ),
    ∀ tolerance : ℝ, 0 < tolerance → ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {scaleRoot boundaryConstant threshold referenceConstant : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ thresholdMax → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 < finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      ∀ weight : ℝ, ({scales with frequency := frequency} : Scales).omega (index.val + 1) ≤ weight →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily
      let second := prepared.referenceWitness.trajectory.movingFamily
      let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
      let centerRadius := factor / 39321600 * changed.location (index.val + 1)
      let patchRadius := factor / 39321600 * changed.length (index.val + 1)
      let moment := fun time => ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖
      let shape := fun time =>
        |(referenceStraightenedShape first.patchMotion graph coordinate index time).1 -
          (referenceStraightenedShape second.patchMotion graph coordinate index time).1| +
        |(referenceStraightenedShape first.patchMotion graph coordinate index time).2 -
          (referenceStraightenedShape second.patchMotion graph coordinate index time).2|
      let velocity := fun time => |relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index time|
      let forcing := fun time =>
        |correctedPaperPhaseForcing changed (phaseCorrection 1 graph) first.patchMotion index time -
          correctedPaperPhaseForcing changed (phaseCorrection 1 graph) second.patchMotion index time|
      let difference := fun time => ∑' power : ℕ,
        ‖quadrupoleExteriorCoefficient changed first.patchMotion index time centerRadius power -
          quadrupoleExteriorCoefficient changed second.patchMotion index time centerRadius power‖
      let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
          second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
      IntervalIntegrable (fun time => Real.exp (-weight * time) *
        |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|)
        volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * velocity time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * shape time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * moment time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) *
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish ∧
      (∀ patch : Fin 4, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish) ∧
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|) ≤
        (1 + tolerance) * changed.omega (index.val + 1) / weight ^ 2 *
          (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * velocity time) +
        tolerance * changed.omega (index.val + 1) / weight *
          (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * shape time) +
        (1 / weight) *
          (tolerance * ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * moment time) +
            (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
            (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * shape time)) +
          constant * changed.omega (index.val + 1) * epsilon *
            ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
              (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
                ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch)) +
          constant * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
          constant * epsilon * ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time) := by
  obtain ⟨correctionSmooth, _, _, _, _, _, _, _⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative coordinateZero coordinateDerivative
  obtain ⟨pointRadius, pointPositive, pointQuarter, pointCap, pointCapPositive, pointFactory⟩ :=
    exists_uniform_actual_cascade_corrected_phase_local_foreign_return correctionSmooth
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, phaseFactory⟩ :=
    exists_uniform_cascade_corrected_phase_weighted_feedback graphAnalytic graphZero graphDerivative coordinateSmooth
      coordinateZero coordinateDerivative
  obtain ⟨momentCap, momentPositive, momentFactory⟩ := exists_uniform_actual_firstMoment_local_foreign_arbitrary_weight_return
  obtain ⟨patchCap, patchPositive, patchFactory⟩ := exists_uniform_actual_foreign_patch_coefficient_integrability
  obtain ⟨inverseRadius, inversePositive, chartConstant, chartOne, inverseBound⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨chartRadius, chartPositive, chartQuarter, closedChart⟩ :=
    exists_uniform_cascade_closed_saddle_dynamics (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
  obtain ⟨forcingRadius, forcingPositive, forcingQuarter, forcingFactory⟩ :=
    exists_uniform_cascade_corrected_phase_forcing_continuity graphAnalytic graphZero graphDerivative coordinateZero coordinateDerivative
  obtain ⟨smoothRadius, smoothPositive, smoothInside⟩ := Metric.mem_nhds_iff.mp
    (correctionSmooth.eventually (by norm_num))
  let rawCap := min pointCap (min momentCap patchCap)
  have capPositive : 0 < rawCap := lt_min pointCapPositive (lt_min momentPositive patchPositive)
  have pointCapBound : rawCap ≤ pointCap := min_le_left _ _
  have momentCapBound : rawCap ≤ momentCap := (min_le_right _ _).trans (min_le_left _ _)
  have patchCapBound : rawCap ≤ patchCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantNonnegative, pointParameters⟩ := pointFactory factorPositive factorSmall
  obtain ⟨momentConstant, momentNonnegative, momentParameters⟩ := momentFactory factorPositive factorSmall
  refine ⟨constant, constantNonnegative, ?_⟩
  intro tolerance tolerancePositive
  obtain ⟨phaseRadius, phasePositive, phaseQuarter, phaseParameters⟩ := phaseFactory tolerance tolerancePositive
  let baseRadius := min pointRadius (min inverseRadius (min chartRadius (min forcingRadius smoothRadius)))
  let radius := min phaseRadius (baseRadius / 2)
  have basePositive : 0 < baseRadius := lt_min pointPositive (lt_min inversePositive (lt_min chartPositive (lt_min forcingPositive smoothPositive)))
  have radiusPositive : 0 < radius := lt_min phasePositive (by positivity)
  have radiusPhase : radius ≤ phaseRadius := min_le_left _ _
  have radiusBase : radius < baseRadius := (min_le_right _ _).trans_lt (by linarith only [basePositive])
  have basePoint : baseRadius ≤ pointRadius := min_le_left _ _
  have baseInverse : baseRadius ≤ inverseRadius := (min_le_right _ _).trans (min_le_left _ _)
  have baseChart : baseRadius ≤ chartRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have baseForcing : baseRadius ≤ forcingRadius := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have baseSmooth : baseRadius ≤ smoothRadius := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let pointTolerance := tolerance / (chartConstant + 1)
  have chartNonnegative : 0 ≤ chartConstant := zero_le_one.trans chartOne
  have pointTolerancePositive : 0 < pointTolerance := by dsimp only [pointTolerance]; positivity
  have pointToleranceBound : pointTolerance ≤ tolerance := by
    exact div_le_self tolerancePositive.le (by linarith only [chartOne])
  have pointChartBound : pointTolerance * chartConstant ≤ tolerance := by
    have identity : pointTolerance * (chartConstant + 1) = tolerance := by
      dsimp only [pointTolerance]
      field_simp
    nlinarith only [identity, pointTolerancePositive]
  refine ⟨radius, radiusPositive, radiusPhase.trans phaseQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant
    rootOne boundaryOne thresholdBound referenceNonnegative
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  filter_upwards [pointParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative pointTolerancePositive,
    phaseParameters scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      factorPositive factorSmall thresholdBound referenceNonnegative,
    momentParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    patchFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne
      factorPositive (factorSmall.trans (by norm_num)),
    forcingFactory scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      factorPositive factorSmall thresholdSmall referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative basePositive,
    scales.eventually_cascade_dilation_closed_physical_history amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)]
    with frequency pointEstimate phaseEstimate momentEstimate patchEstimate forcingEstimate referenceSmall physicalHistory lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishPositive finishBound radialSmall small
  obtain ⟨lift, liftContinuous, polar, weighted⟩ := phaseEstimate prepared.toCascadeMaterialPreparedPair path index nonterminal
    finish finishPositive finishBound (fun time inside => (small time inside).trans radiusPhase)
  refine ⟨lift, liftContinuous, polar, ?_⟩
  intro weight weightBound
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let centerRadius := factor / 39321600 * changed.location (index.val + 1)
  let patchRadius := factor / 39321600 * changed.length (index.val + 1)
  let center := fun time => prepared.rawSourceCenteredState time index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let moment := fun time => ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖
  let shape := fun time =>
    |(referenceStraightenedShape first.patchMotion graph coordinate index time).1 -
      (referenceStraightenedShape second.patchMotion graph coordinate index time).1| +
    |(referenceStraightenedShape first.patchMotion graph coordinate index time).2 -
      (referenceStraightenedShape second.patchMotion graph coordinate index time).2|
  let velocity := fun time => |relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index time|
  let forcing := fun time => |correctedPaperPhaseForcing changed (phaseCorrection 1 graph) first.patchMotion index time -
    correctedPaperPhaseForcing changed (phaseCorrection 1 graph) second.patchMotion index time|
  let difference := fun time => ∑' power : ℕ,
    ‖quadrupoleExteriorCoefficient changed first.patchMotion index time centerRadius power -
      quadrupoleExteriorCoefficient changed second.patchMotion index time centerRadius power‖
  let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have weightPositive : 0 < weight := omegaPositive.trans_le weightBound
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| < baseRadius := by
    fin_cases side
    · exact (small time inside).trans_lt radiusBase
    · have sharp := referenceSmall prepared.toCascadeMaterialPreparedPair time
        (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < baseRadius
      linarith only [sharp, abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)]
  have chartContinuous : ContinuousOn (fun time =>
      referenceStraightenedShape first.patchMotion graph coordinate index time -
        referenceStraightenedShape second.patchMotion graph coordinate index time) (Icc 0 finish) := by
    intro time inside
    have actual := (closedChart prepared.toCascadeMaterialPreparedPair path index time (subset inside)
      (fun side => (pairedSmall side time inside).trans_le baseChart)).continuousAt.continuousWithinAt (s := Icc (0 : ℝ) finish)
    simpa only [first, second, prepared.referenceIdentity] using actual
  have shapeContinuous : ContinuousOn shape (Icc 0 finish) := chartContinuous.fst.abs.add chartContinuous.snd.abs
  have shapeIntegrable := (weightContinuous.continuousOn.mul shapeContinuous).intervalIntegrable_of_Icc (μ := volume) finishPositive.le
  have positions (side : Fin 2) (patch : Fin 4) :
      Continuous (fun time => patchCentroid (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index patch) := by
    fin_cases side
    · exact first.patchCentroid_continuous index patch
    · simpa only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] using second.patchCentroid_continuous index patch
  have correctedContinuous (side : Fin 2) : ContinuousOn
      (correctedPaperPhase (phaseCorrection 1 graph) (lift side)
        (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) index) (Icc 0 finish) := by
    apply correctedPaperPhase_continuousOn_of_centroids _ _ _ _ (fun patch => (positions side patch).continuousOn)
      (liftContinuous side).1.continuousOn (fun time inside => (pairedSmall side time inside).le.trans (basePoint.trans pointQuarter))
    intro time inside
    have smooth : ContDiffAt ℝ 2 (phaseCorrection 1 graph)
        (unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index) := by
      apply smoothInside
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      exact (le_add_of_nonneg_right (abs_nonneg _)).trans_lt ((pairedSmall side time inside).trans_le baseSmooth)
    exact smooth.continuousAt
  have correctedDifferenceContinuous : ContinuousOn
      (relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index)
      (Icc 0 finish) := (correctedContinuous 0).sub (correctedContinuous 1)
  have correctedIntegrable :=
    (weightContinuous.continuousOn.mul correctedDifferenceContinuous.abs).intervalIntegrable_of_Icc (μ := volume) finishPositive.le
  have pointForcing := forcingEstimate prepared.toCascadeMaterialPreparedPair path index finish finishPositive finishBound
    (fun time inside => (small time inside).trans (radiusBase.le.trans baseForcing))
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) := by
    simpa only [forcing, first, second, cascadePairedMotion, Fin.cases_zero, Fin.cases_succ, prepared.referenceIdentity] using
      ((pointForcing 0).sub (pointForcing 1)).abs
  have forcingIntegrable := (weightContinuous.continuousOn.mul forcingContinuous).intervalIntegrable_of_Icc (μ := volume) finishPositive.le
  let dilation := fun time => (diagonalDifference first.patchMotion time index - diagonalDifference second.patchMotion time index) /
    changed.length (index.val + 1) ^ 2
  let mechanical := fun time => (prepared.toCascadeMaterialPreparedPair.pairedDiagonalVelocity 0 index time -
    prepared.toCascadeMaterialPreparedPair.pairedDiagonalVelocity 1 index time) / changed.length (index.val + 1) ^ 2
  have physicalDerivative (time : ℝ) (inside : time ∈ Icc 0 finish) :
      HasDerivAt dilation (relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index time) time := by
    simpa only [dilation, first, second, prepared.referenceIdentity] using
      (physicalHistory prepared.toCascadeMaterialPreparedPair path index nonterminal time (subset inside)).1
  have mechanicalDerivative (time : ℝ) (inside : time ∈ Icc 0 finish) : HasDerivAt dilation (mechanical time) time := by
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith only [inside.1], by linarith only [inside.2, finishBound, path.stopBound]⟩
    simpa only [dilation, mechanical, first, second, cascadePairedMotion, Fin.cases_zero, Fin.cases_succ,
      prepared.referenceIdentity] using
      ((prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 0 index globalInside).sub
        (prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 1 index globalInside)).div_const
        (changed.length (index.val + 1) ^ 2)
  have mechanicalContinuous : Continuous mechanical :=
    ((prepared.toCascadeMaterialPreparedPair.pairedDiagonalVelocity_continuous 0 index).sub
      (prepared.toCascadeMaterialPreparedPair.pairedDiagonalVelocity_continuous 1 index)).div_const _
  have velocityContinuous : ContinuousOn velocity (Icc 0 finish) :=
    (mechanicalContinuous.continuousOn.congr (fun time inside =>
      (physicalDerivative time inside).unique (mechanicalDerivative time inside))).abs
  have velocityIntegrable := (weightContinuous.continuousOn.mul velocityContinuous).intervalIntegrable_of_Icc (μ := volume) finishPositive.le
  let momentPrepared := prepared.enlargeCap momentCapBound
  obtain ⟨differenceIntegrable, _, centerIntegrable, rawIntegrable, momentIntegrable, _⟩ :=
    momentEstimate count phase dipoleAngle momentPrepared path index nonterminal finish finishPositive.le finishBound radialSmall weight weightBound
  have centerI : IntervalIntegrable (fun time => Real.exp (-weight * time) * center time) volume 0 finish := by
    with_reducible_and_instances
      dsimp only [center, momentPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
        at centerIntegrable ⊢
      exact centerIntegrable
  have rawI : IntervalIntegrable (fun time => Real.exp (-weight * time) * raw time) volume 0 finish := by
    with_reducible_and_instances
      dsimp only [raw, momentPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
        at rawIntegrable ⊢
      exact rawIntegrable
  have differenceI : IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish := by
    simpa only [difference, centerRadius, first, second, momentPrepared, CascadeSourcePreparedPair.enlargeCap] using differenceIntegrable
  have momentI : IntervalIntegrable (fun time => Real.exp (-weight * time) * moment time) volume 0 finish := by
    simpa only [moment, first, second, momentPrepared, CascadeSourcePreparedPair.enlargeCap, prepared.referenceIdentity] using momentIntegrable
  let patchPrepared := prepared.enlargeCap patchCapBound
  have patchRadiusNonnegative : 0 ≤ patchRadius :=
    mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.length_pos _).le
  have patchRadiusSmall : patchRadius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    have lengthBound := (lengths (index.val + 1)).le
    change changed.length (index.val + 1) ≤ 1 * changed.location (index.val + 1) at lengthBound
    have numeric : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorSmall]
    calc
      _ ≤ (factor / 39321600) * changed.location (index.val + 1) :=
        mul_le_mul_of_nonneg_left (by simpa only [one_mul] using lengthBound) (by positivity)
      _ ≤ (1 / (100000 * 96)) * changed.location (index.val + 1) :=
        mul_le_mul_of_nonneg_right numeric (changed.location_pos _).le
      _ = _ := by dsimp only [changed, Scales.location]; ring
  have foreignI (patch : Fin 4) : IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish := by
    have actual := (patchEstimate count phase dipoleAngle patchPrepared path (index, patch) patchRadius patchRadiusNonnegative
      patchRadiusSmall finish finishPositive.le finishBound weight).2.2
    simpa only [foreign, first, second, patchPrepared, CascadeSourcePreparedPair.enlargeCap] using actual
  have unstableBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape first.patchMotion time index - unstableShape second.patchMotion time index| ≤ chartConstant * shape time := by
    have actual := inverseBound
      (unstableShape first.patchMotion time index, stableShape first.patchMotion time index)
      (unstableShape second.patchMotion time index, stableShape second.patchMotion time index)
      (by simpa only [first] using (pairedSmall 0 time inside).trans_le baseInverse)
      (by simpa only [second, cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] using
        (pairedSmall 1 time inside).trans_le baseInverse)
    have normBound :
        ‖localNormalFormChart graph coordinate (unstableShape first.patchMotion time index, stableShape first.patchMotion time index) -
          localNormalFormChart graph coordinate (unstableShape second.patchMotion time index, stableShape second.patchMotion time index)‖ ≤ shape time := by
      dsimp only [shape, referenceStraightenedShape]
      rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans
      (actual.trans (mul_le_mul_of_nonneg_left normBound chartNonnegative))
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) :
      forcing time ≤ tolerance * (moment time + center time + shape time) +
        constant * changed.omega (index.val + 1) * epsilon * (center time + raw time) +
        constant * difference time + constant * epsilon * ∑ patch, foreign patch time := by
    have actual := pointEstimate count phase dipoleAngle (prepared.enlargeCap pointCapBound) path index nonterminal finish
      finishPositive.le finishBound radialSmall time inside (fun side => (pairedSmall side time inside).le.trans basePoint)
    have normalized : forcing time ≤ pointTolerance *
        (moment time + center time + |unstableShape first.patchMotion time index - unstableShape second.patchMotion time index|) +
        constant * changed.omega (index.val + 1) * epsilon * (center time + raw time) +
        constant * difference time + constant * epsilon * ∑ patch, foreign patch time := by
      with_reducible_and_instances
        dsimp only [forcing, moment, first, second, center, raw, difference, centerRadius, epsilon, foreign, patchRadius,
          CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState,
          CascadeSourcePreparedPair.rawSourceShapeBudget, MovingCentroidGaugeTrajectory.spectralCoordinate] at actual ⊢
        exact actual
    have toleranceBound := phase_chart_tolerance_arbitrary_weight (moment := moment time) (center := center time) (shape := shape time)
      pointTolerancePositive.le pointToleranceBound pointChartBound
      (norm_nonneg _) (div_nonneg (norm_nonneg _) (changed.length_pos _).le)
      (add_nonneg (abs_nonneg _) (abs_nonneg _)) (unstableBound time inside)
    exact normalized.trans (add_le_add_right (add_le_add_right (add_le_add_right toleranceBound _) _) _)
  have forcingBound := weighted_phase_forcing_local_foreign_arbitrary_weight finishPositive.le momentI centerI shapeIntegrable rawI
    differenceI foreignI forcingIntegrable pointwise
  have phaseBound := weighted weight weightPositive
  have omegaAbs : |({scales with frequency := frequency} : Scales).omega (index.val + 1)| =
      changed.omega (index.val + 1) := abs_of_pos omegaPositive
  have normalizedPhaseBound :
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|) ≤
        (1 + tolerance) * changed.omega (index.val + 1) / weight ^ 2 *
          (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * velocity time) +
        tolerance * changed.omega (index.val + 1) / weight *
          (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * shape time) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time) / weight := by
    simpa only [velocity, shape, forcing, first, second, prepared.referenceIdentity, omegaAbs] using phaseBound
  refine ⟨correctedIntegrable, velocityIntegrable, shapeIntegrable, forcingIntegrable, momentI, centerI, rawI, differenceI, foreignI, ?_⟩
  have actual := normalizedPhaseBound.trans (add_le_add_left
    (div_le_div_of_nonneg_right forcingBound weightPositive.le) _)
  convert actual using 1; dsimp only [center, raw]; ring

end EulerNonuniqueness.Paper


