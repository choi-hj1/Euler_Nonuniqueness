import EulerNonuniqueness.Section5.CascadeCorrectedPhaseLocalForeignWeightedReturn
import EulerNonuniqueness.Section5.CascadeCorrectedPhaseLiftJet
import Mathlib.Analysis.Calculus.FDeriv.Measurable

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem intervalIntegrable_remove_exponential {value : ℝ → ℝ} {weight start finish : ℝ}
    (integrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * value time) volume start finish) :
    IntervalIntegrable value volume start finish := by
  have continuous : Continuous (fun time : ℝ => Real.exp (weight * time)) := by fun_prop
  have actual := integrable.mul_continuousOn continuous.continuousOn
  have identity (time : ℝ) : (Real.exp (-weight * time) * value time) * Real.exp (weight * time) = value time := by
    calc
      _ = (Real.exp (-weight * time) * Real.exp (weight * time)) * value time := by ring
      _ = _ := by rw [← Real.exp_add, show -weight * time + weight * time = 0 by ring, Real.exp_zero, one_mul]
  simpa only [identity] using actual

private theorem phase_history_of_integrable_majorant {phase velocity upper : ℝ → ℝ} {finish : ℝ}
    (ordered : 0 ≤ finish) (continuous : ContinuousOn phase (Icc 0 finish)) (initial : phase 0 = 0)
    (derivative : ∀ time ∈ Ioo 0 finish, HasDerivAt phase (velocity time) time)
    (upperIntegrable : IntervalIntegrable upper volume 0 finish)
    (bound : ∀ time ∈ Icc 0 finish, |velocity time| ≤ upper time) :
    IntervalIntegrable velocity volume 0 finish ∧
      ∀ time ∈ Icc 0 finish, phase time = ∫ current in (0 : ℝ)..time, velocity current ∧
        |phase time| ≤ ∫ current in (0 : ℝ)..time, upper current := by
  have measurable : AEStronglyMeasurable velocity (volume.restrict (uIoc 0 finish)) := by
    rw [uIoc_of_le ordered]
    apply (aestronglyMeasurable_deriv phase (volume.restrict (Ioc 0 finish))).congr
    have almostDifferent : ∀ᵐ time : ℝ ∂volume, time ≠ finish := by simp [ae_iff]
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae almostDifferent] with time inside different
    exact (derivative time ⟨inside.1, lt_of_le_of_ne inside.2 different⟩).deriv
  have velocityIntegrable : IntervalIntegrable velocity volume 0 finish :=
    upperIntegrable.mono_fun' measurable (by
      rw [uIoc_of_le ordered]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with time inside
      simpa only [Real.norm_eq_abs] using bound time ⟨inside.1.le, inside.2⟩)
  refine ⟨velocityIntegrable, ?_⟩
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have unorderedSubset : uIcc (0 : ℝ) time ⊆ uIcc 0 finish := by
    rw [uIcc_of_le inside.1, uIcc_of_le ordered]
    exact subset
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1 (continuous.mono subset)
    (fun current member => derivative current ⟨member.1, member.2.trans_le inside.2⟩)
    (velocityIntegrable.mono_set unorderedSubset)
  rw [initial, sub_zero] at integral
  refine ⟨integral.symm, ?_⟩
  rw [← integral]
  exact (intervalIntegral.abs_integral_le_integral_abs inside.1).trans
    (intervalIntegral.integral_mono_on (μ := volume) inside.1
      (velocityIntegrable.abs.mono_set unorderedSubset) (upperIntegrable.mono_set unorderedSubset)
      (fun current member => bound current (subset member)))

private theorem history_chart_tolerance
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

theorem exists_uniform_actual_cascade_corrected_phase_local_foreign_history
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
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
        (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index 0 = 0 ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let omega := changed.omega (index.val + 1)
      let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
      let centerRadius := factor / 39321600 * changed.location (index.val + 1)
      let patchRadius := factor / 39321600 * changed.length (index.val + 1)
      let dilation := fun time => |(diagonalDifference first time index - diagonalDifference second time index) /
        changed.length (index.val + 1) ^ 2|
      let shape := fun time =>
        |(referenceStraightenedShape first graph coordinate index time).1 -
          (referenceStraightenedShape second graph coordinate index time).1| +
        |(referenceStraightenedShape first graph coordinate index time).2 -
          (referenceStraightenedShape second graph coordinate index time).2|
      let moment := fun time => ‖relativeNormalizedFirstMoment changed first second index time‖
      let center := fun time => prepared.rawSourceCenteredState time index
      let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
      let difference := fun time => ∑' power : ℕ,
        ‖quadrupoleExteriorCoefficient changed first index time centerRadius power -
          quadrupoleExteriorCoefficient changed second index time centerRadius power‖
      let firstFamily := prepared.trajectory.movingFamily
      let secondFamily := prepared.referenceWitness.trajectory.movingFamily
      let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖firstFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid firstFamily.patchMotion current index patch) patchRadius (power + 1) time -
          secondFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid secondFamily.patchMotion current index patch) patchRadius (power + 1) time‖
      let upper := fun time => (1 + tolerance) * omega * dilation time + tolerance * omega * shape time +
        tolerance * (moment time + center time + shape time) +
        constant * omega * epsilon * (center time + raw time) + constant * difference time +
        constant * epsilon * ∑ patch : Fin 4, foreign patch time
      let phaseCurve := relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
        (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index
      let phaseVelocity := relativeCorrectedPaperPhaseVelocity changed (phaseCorrection 1 graph)
        (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index
      IntervalIntegrable dilation volume 0 finish ∧ IntervalIntegrable shape volume 0 finish ∧
      IntervalIntegrable moment volume 0 finish ∧ IntervalIntegrable center volume 0 finish ∧
      IntervalIntegrable raw volume 0 finish ∧ IntervalIntegrable difference volume 0 finish ∧
      (∀ patch : Fin 4, IntervalIntegrable (foreign patch) volume 0 finish) ∧
      IntervalIntegrable upper volume 0 finish ∧ IntervalIntegrable phaseVelocity volume 0 finish ∧
      ∀ time ∈ Icc 0 finish, phaseCurve time = ∫ current in (0 : ℝ)..time, phaseVelocity current ∧
        |phaseCurve time| ≤ ∫ current in (0 : ℝ)..time, upper current := by
  obtain ⟨weightedThreshold, weightedThresholdPositive, weightedThresholdEighth, weightedCap, weightedCapPositive, weightedFactory⟩ :=
    exists_uniform_actual_cascade_corrected_phase_local_foreign_weighted_return graphAnalytic graphZero graphDerivative
      coordinateSmooth coordinateZero coordinateDerivative
  obtain ⟨shearThreshold, shearThresholdPositive, shearThresholdEighth, shearFactory⟩ :=
    exists_uniform_cascade_corrected_phase_small_shear graphAnalytic graphZero graphDerivative coordinateSmooth
      coordinateZero coordinateDerivative
  obtain ⟨correctionSmooth, _, _, _, _, _, _, _⟩ :=
    sameGraph_phaseCorrection_exists_uniform_stable_factor graphAnalytic graphZero graphDerivative coordinateZero coordinateDerivative
  obtain ⟨pointRadius, pointPositive, pointQuarter, pointCap, pointCapPositive, pointFactory⟩ :=
    exists_uniform_actual_cascade_corrected_phase_local_foreign_return correctionSmooth
  obtain ⟨jetConstant, jetNonnegative, jetRadius, jetPositive, jetQuarter, jets⟩ :=
    exists_uniform_cascade_sameGraph_corrected_phase_lift_jet graphAnalytic graphZero graphDerivative coordinateZero coordinateDerivative
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseBound⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz (graphAnalytic.contDiffAt (n := 2)) coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨smoothRadius, smoothPositive, smoothInside⟩ := Metric.mem_nhds_iff.mp
    (correctionSmooth.eventually (by norm_num))
  let thresholdMax := min weightedThreshold shearThreshold
  let rawCap := min weightedCap pointCap
  have capPositive : 0 < rawCap := lt_min weightedCapPositive pointCapPositive
  have thresholdPositive : 0 < thresholdMax := lt_min weightedThresholdPositive shearThresholdPositive
  have thresholdEighth : thresholdMax ≤ 1 / 8 := (min_le_left _ _).trans weightedThresholdEighth
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨weightedConstant, weightedNonnegative, weightedParameters⟩ := weightedFactory factorPositive factorSmall
  obtain ⟨constant, constantNonnegative, pointParameters⟩ := pointFactory factorPositive factorSmall
  refine ⟨constant, constantNonnegative, ?_⟩
  intro tolerance tolerancePositive
  obtain ⟨weightedRadius, weightedPositive, weightedQuarter, weightedParameters⟩ := weightedParameters tolerance tolerancePositive
  obtain ⟨shearRadius, shearPositive, shearQuarter, shearParameters⟩ := shearFactory tolerance tolerancePositive
  let baseRadius := min pointRadius (min inverseRadius (min jetRadius smoothRadius))
  let radius := min weightedRadius (min shearRadius (baseRadius / 2))
  have basePositive : 0 < baseRadius := lt_min pointPositive (lt_min inversePositive (lt_min jetPositive smoothPositive))
  have radiusPositive : 0 < radius := lt_min weightedPositive (lt_min shearPositive (by positivity))
  have radiusWeighted : radius ≤ weightedRadius := min_le_left _ _
  have radiusShear : radius ≤ shearRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusBase : radius < baseRadius :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith only [basePositive])
  have basePoint : baseRadius ≤ pointRadius := min_le_left _ _
  have baseInverse : baseRadius ≤ inverseRadius := (min_le_right _ _).trans (min_le_left _ _)
  have baseJet : baseRadius ≤ jetRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have baseSmooth : baseRadius ≤ smoothRadius := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let pointTolerance := tolerance / (inverseConstant + 1)
  have inverseNonnegative : 0 ≤ inverseConstant := zero_le_one.trans inverseOne
  have pointTolerancePositive : 0 < pointTolerance := by dsimp only [pointTolerance]; positivity
  have pointToleranceBound : pointTolerance ≤ tolerance :=
    div_le_self tolerancePositive.le (by linarith only [inverseOne])
  have pointInverseBound : pointTolerance * inverseConstant ≤ tolerance := by
    have identity : pointTolerance * (inverseConstant + 1) = tolerance := by dsimp only [pointTolerance]; field_simp
    nlinarith only [identity, pointTolerancePositive]
  refine ⟨radius, radiusPositive, radiusWeighted.trans weightedQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant
    rootOne boundaryOne thresholdBound referenceNonnegative
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  filter_upwards [weightedParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      (thresholdBound.trans (min_le_left _ _)) referenceNonnegative,
    pointParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative pointTolerancePositive,
    shearParameters scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorSmall
      (thresholdBound.trans (min_le_right _ _)) referenceNonnegative,
    jets scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive factorSmall
      thresholdSmall referenceNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative basePositive,
    eventually_gt_atTop (0 : ℝ)] with frequency weightedEstimate pointEstimate shearEstimate jetEstimate referenceSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let firstFamily := prepared.trajectory.movingFamily
  let secondFamily := prepared.referenceWitness.trajectory.movingFamily
  let omega := changed.omega (index.val + 1)
  let weight := 2 * Real.sqrt 2 * omega
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let centerRadius := factor / 39321600 * changed.location (index.val + 1)
  let patchRadius := factor / 39321600 * changed.length (index.val + 1)
  let signedDilation := fun time => (diagonalDifference first time index - diagonalDifference second time index) /
    changed.length (index.val + 1) ^ 2
  let dilation := fun time => |signedDilation time|
  let shape := fun time =>
    |(referenceStraightenedShape first graph coordinate index time).1 -
      (referenceStraightenedShape second graph coordinate index time).1| +
    |(referenceStraightenedShape first graph coordinate index time).2 -
      (referenceStraightenedShape second graph coordinate index time).2|
  let moment := fun time => ‖relativeNormalizedFirstMoment changed first second index time‖
  let center := fun time => prepared.rawSourceCenteredState time index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let difference := fun time => ∑' power : ℕ,
    ‖quadrupoleExteriorCoefficient changed first index time centerRadius power -
      quadrupoleExteriorCoefficient changed second index time centerRadius power‖
  let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖firstFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid firstFamily.patchMotion current index patch) patchRadius (power + 1) time -
      secondFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid secondFamily.patchMotion current index patch) patchRadius (power + 1) time‖
  let forcing := fun time => |correctedPaperPhaseForcing changed (phaseCorrection 1 graph) first index time -
    correctedPaperPhaseForcing changed (phaseCorrection 1 graph) second index time|
  let upper := fun time => (1 + tolerance) * omega * dilation time + tolerance * omega * shape time +
    tolerance * (moment time + center time + shape time) +
    constant * omega * epsilon * (center time + raw time) + constant * difference time +
    constant * epsilon * ∑ patch : Fin 4, foreign patch time
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| +
        |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index| < baseRadius := by
    fin_cases side
    · exact (small time inside).trans_lt radiusBase
    · have sharp := referenceSmall prepared.toCascadeMaterialPreparedPair time
        (show time ∈ Icc (0 : ℝ) 1 from ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩) index
      change |unstableShape second time index| + |stableShape second time index| < baseRadius
      linarith only [sharp, abs_nonneg (diagonalDifference second time index / changed.length (index.val + 1) ^ 2 - 1)]
  obtain ⟨lift, liftContinuous, initial, polar, phaseJet, literalDerivative, _⟩ :=
    jetEstimate prepared.toCascadeMaterialPreparedPair path index nonterminal finish finishNonnegative finishBound
      (fun side time inside => (pairedSmall side time inside).trans_le baseJet)
  refine ⟨lift, liftContinuous, initial, polar, ?_⟩
  dsimp only
  let phaseCurve := relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
    (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index
  let phaseVelocity := relativeCorrectedPaperPhaseVelocity changed (phaseCorrection 1 graph)
    (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index
  have inputs : IntervalIntegrable shape volume 0 finish ∧ IntervalIntegrable moment volume 0 finish ∧
      IntervalIntegrable center volume 0 finish ∧ IntervalIntegrable raw volume 0 finish ∧
      IntervalIntegrable difference volume 0 finish ∧ (∀ patch : Fin 4, IntervalIntegrable (foreign patch) volume 0 finish) := by
    by_cases finishZero : finish = 0
    · subst finish
      simp
    have finishPositive : 0 < finish := lt_of_le_of_ne finishNonnegative (Ne.symm finishZero)
    let weightedPrepared := prepared.enlargeCap (min_le_left weightedCap pointCap)
    obtain ⟨weightedLift, _, _, _, _, shapeI, _, momentI, centerI, rawI, differenceI, foreignI, _⟩ :=
      weightedEstimate count phase dipoleAngle weightedPrepared path index nonterminal finish finishPositive finishBound
        radialSmall (fun time inside => (small time inside).trans radiusWeighted)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply intervalIntegrable_remove_exponential (weight := weight)
      simpa only [shape, first, second, prepared.referenceIdentity, weightedPrepared, CascadeSourcePreparedPair.enlargeCap] using shapeI
    · apply intervalIntegrable_remove_exponential (weight := weight)
      simpa only [moment, first, second, prepared.referenceIdentity, weightedPrepared, CascadeSourcePreparedPair.enlargeCap] using momentI
    · apply intervalIntegrable_remove_exponential (weight := weight)
      with_reducible_and_instances
        dsimp only [center, weightedPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState] at centerI ⊢
        exact centerI
    · apply intervalIntegrable_remove_exponential (weight := weight)
      with_reducible_and_instances
        dsimp only [raw, weightedPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget] at rawI ⊢
        exact rawI
    · apply intervalIntegrable_remove_exponential (weight := weight)
      simpa only [difference, centerRadius, first, second, prepared.referenceIdentity, weightedPrepared, CascadeSourcePreparedPair.enlargeCap] using differenceI
    · intro patch
      apply intervalIntegrable_remove_exponential (weight := weight)
      simpa only [foreign, patchRadius, firstFamily, secondFamily, weightedPrepared, CascadeSourcePreparedPair.enlargeCap] using foreignI patch
  obtain ⟨shapeIntegrable, momentIntegrable, centerIntegrable, rawIntegrable, differenceIntegrable, foreignIntegrable⟩ := inputs
  have signedDilationContinuous : ContinuousOn signedDilation (Icc 0 finish) := by
    intro time inside
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith only [inside.1], by linarith only [inside.2, finishBound, path.stopBound]⟩
    have derivative := ((prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 0 index globalInside).sub
      (prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 1 index globalInside)).div_const
      (changed.length (index.val + 1) ^ 2)
    simpa only [signedDilation, first, second, cascadePairedMotion, Fin.cases_zero, Fin.cases_succ] using
      derivative.continuousAt.continuousWithinAt (s := Icc (0 : ℝ) finish)
  have dilationIntegrable : IntervalIntegrable dilation volume 0 finish :=
    signedDilationContinuous.abs.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have positions (side : Fin 2) (patch : Fin 4) :
      Continuous (fun time => patchCentroid (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index patch) := by
    fin_cases side
    · exact firstFamily.patchCentroid_continuous index patch
    · simpa only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] using secondFamily.patchCentroid_continuous index patch
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
  have curveContinuous : ContinuousOn phaseCurve (Icc 0 finish) := (correctedContinuous 0).sub (correctedContinuous 1)
  have unstableBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape first time index - unstableShape second time index| ≤ inverseConstant * shape time := by
    have actual := inverseBound (unstableShape first time index, stableShape first time index)
      (unstableShape second time index, stableShape second time index)
      ((pairedSmall 0 time inside).trans_le baseInverse) ((pairedSmall 1 time inside).trans_le baseInverse)
    have normBound : ‖localNormalFormChart graph coordinate (unstableShape first time index, stableShape first time index) -
        localNormalFormChart graph coordinate (unstableShape second time index, stableShape second time index)‖ ≤ shape time := by
      dsimp only [shape, referenceStraightenedShape]
      rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans
      (actual.trans (mul_le_mul_of_nonneg_left normBound inverseNonnegative))
  have pointForcing (time : ℝ) (inside : time ∈ Icc 0 finish) :
      forcing time ≤ tolerance * (moment time + center time + shape time) +
        constant * omega * epsilon * (center time + raw time) + constant * difference time +
        constant * epsilon * ∑ patch, foreign patch time := by
    have actual := pointEstimate count phase dipoleAngle (prepared.enlargeCap (min_le_right weightedCap pointCap)) path index nonterminal
      finish finishNonnegative finishBound radialSmall time inside (fun side => (pairedSmall side time inside).le.trans basePoint)
    have normalized : forcing time ≤ pointTolerance *
        (moment time + center time + |unstableShape first time index - unstableShape second time index|) +
        constant * omega * epsilon * (center time + raw time) + constant * difference time +
        constant * epsilon * ∑ patch, foreign patch time := by
      with_reducible_and_instances
        dsimp only [forcing, moment, first, second, center, raw, difference, centerRadius, omega, epsilon, foreign, patchRadius,
          firstFamily, secondFamily, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState,
          CascadeSourcePreparedPair.rawSourceShapeBudget, MovingCentroidGaugeTrajectory.spectralCoordinate] at actual ⊢
        rw [prepared.referenceIdentity]
        exact actual
    have toleranceBound := history_chart_tolerance (moment := moment time) (center := center time) (shape := shape time)
      pointTolerancePositive.le pointToleranceBound pointInverseBound (norm_nonneg _)
      (div_nonneg (norm_nonneg _) (changed.length_pos _).le) (add_nonneg (abs_nonneg _) (abs_nonneg _)) (unstableBound time inside)
    exact normalized.trans (add_le_add_right (add_le_add_right (add_le_add_right toleranceBound _) _) _)
  have velocityBound (time : ℝ) (inside : time ∈ Icc 0 finish) : |phaseVelocity time| ≤ upper time := by
    have shear := shearEstimate prepared.toCascadeMaterialPreparedPair path index nonterminal finish finishNonnegative finishBound
      (fun current member => (small current member).trans radiusShear) time inside
    change |phaseVelocity time - omega * signedDilation time| ≤
      tolerance * |omega| * (|signedDilation time| + shape time) + forcing time at shear
    rw [abs_of_pos omegaPositive] at shear
    have triangle := abs_add (omega * signedDilation time) (phaseVelocity time - omega * signedDilation time)
    rw [show omega * signedDilation time + (phaseVelocity time - omega * signedDilation time) = phaseVelocity time by ring,
      abs_mul, abs_of_pos omegaPositive] at triangle
    have combined := triangle.trans (add_le_add_left shear _)
    have normalized : |phaseVelocity time| ≤ (1 + tolerance) * omega * dilation time +
        tolerance * omega * shape time + forcing time := by
      convert combined using 1 <;> dsimp only [dilation] <;> ring
    exact normalized.trans (by
      convert add_le_add_left (pointForcing time inside)
        ((1 + tolerance) * omega * dilation time + tolerance * omega * shape time) using 1 <;> dsimp only [upper] <;> ring)
  have foreignSumIntegrable : IntervalIntegrable (fun time => ∑ patch, foreign patch time) volume 0 finish := by
    simpa only [Finset.sum_apply] using
      (IntervalIntegrable.sum Finset.univ (f := foreign) (fun patch _ => foreignIntegrable patch))
  have upperIntegrable : IntervalIntegrable upper volume 0 finish := by
    convert (((((dilationIntegrable.const_mul ((1 + tolerance) * omega)).add
      (shapeIntegrable.const_mul (tolerance * omega))).add
      (((momentIntegrable.add centerIntegrable).add shapeIntegrable).const_mul tolerance)).add
      ((centerIntegrable.add rawIntegrable).const_mul (constant * omega * epsilon))).add
      (differenceIntegrable.const_mul constant)).add (foreignSumIntegrable.const_mul (constant * epsilon)) using 1
  have history := phase_history_of_integrable_majorant finishNonnegative curveContinuous initial literalDerivative upperIntegrable velocityBound
  exact ⟨dilationIntegrable, shapeIntegrable, momentIntegrable, centerIntegrable, rawIntegrable, differenceIntegrable,
    foreignIntegrable, upperIntegrable, history.1, history.2⟩

end EulerNonuniqueness.Paper

