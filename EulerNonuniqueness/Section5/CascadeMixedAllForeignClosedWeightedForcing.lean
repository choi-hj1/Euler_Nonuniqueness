import EulerNonuniqueness.Section5.CascadeMixedFollowerClosedWeightedForcing
import EulerNonuniqueness.Section5.CascadeMixedSelectedFinerOriginalPrefixBudget

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem all_foreign_feedback_scalar
    {allValue shape finer macroValue common sharp first returned small macroShape macroFeedback tolerance : ℝ}
    (allNonnegative : 0 ≤ allValue) (shapeNonnegative : 0 ≤ shape) (smallNonnegative : 0 ≤ small)
    (firstBound : allValue ≤ first * shape + 4 * finer + returned * common)
    (sharpBound : finer ≤ sharp + small * macroValue)
    (macroBound : macroValue ≤ macroShape * shape + macroFeedback * allValue)
    (feedbackBound : 4 * small * macroFeedback ≤ 1 / 2)
    (shapeBound : 2 * (first + 4 * small * macroShape) ≤ tolerance) :
    allValue ≤ tolerance * shape + 8 * sharp + 2 * returned * common := by
  have scaledSharp := mul_le_mul_of_nonneg_left sharpBound (by norm_num : (0 : ℝ) ≤ 4)
  have scaledMacro := mul_le_mul_of_nonneg_left macroBound (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) smallNonnegative)
  have scaledFeedback := mul_le_mul_of_nonneg_right feedbackBound allNonnegative
  have scaledShape := mul_le_mul_of_nonneg_right shapeBound shapeNonnegative
  nlinarith only [firstBound, scaledSharp, scaledMacro, scaledFeedback, scaledShape]

theorem exists_uniform_actual_mixed_all_foreign_closed_weighted_forcing
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ commonIncoming ≥ (0 : ℝ), ∃ commonOutgoing ≥ (0 : ℝ),
    ∃ sharpIncoming ≥ (0 : ℝ), ∃ sharpOutgoing ≥ (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ followerConstant ≥ (1 : ℝ),
    ∃ ratioMin ≥ max 2 (4 * followerConstant), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → ∀ extent : ℝ, 1 ≤ extent →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude →
    ∀ threshold ≤ thresholdMax, ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant tolerance : ℝ),
    1 ≤ boundaryConstant → 0 < tolerance →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ drive : Fin count, drive.val + 1 < count → ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ path.stop →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, drive.val < source.val →
      let length := changed.length (source.val + 1)
      0 ≤ entry source ∧ entry source ≤ terminal ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entry source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion (entry source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
          secondDipoleCenter motion (entry source) source)).re ∧
      ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
        (5 / 4 : ℝ) * length * initialDistance source) →
    (∀ source : Fin count, drive.val < source.val → ∀ time ∈ Icc 0 (entry source),
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
        extent * changed.length (source.val + 1))) →
    ∀ coefficient : ℝ, 0 < coefficient → ∀ magnitude : Fin count → ℝ,
    let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    (∀ source : Fin count, drive.val < source.val → 0 ≤ magnitude source ∧ ∀ time ∈ Icc 0 (entry source),
      sharpState source time ≤ magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    ∀ finish ∈ Icc 0 terminal,
    (∀ time ∈ Icc 0 finish, |radialShape motion time drive| ≤ 1 / 2) →
    (∀ time ∈ Icc 0 finish, |unstableShape motion time drive| + |stableShape motion time drive| ≤ radius) →
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time receiver| + |stableShape motion time receiver| ≤ radius) →
    ∀ weight : ℝ, changed.omega (drive.val + 1) ≤ weight →
    (∀ source : Fin count, drive.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let allForcing := prepared.selectedForeignForcing (Finset.univ.erase drive) drive
    let shape := fun time =>
      |(referenceStraightenedShape motion graph coordinate drive time).1 -
        (referenceStraightenedShape prepared.referenceWitness.trajectory.movingFamily.patchMotion graph coordinate drive time).1| +
      |(referenceStraightenedShape motion graph coordinate drive time).2 -
        (referenceStraightenedShape prepared.referenceWitness.trajectory.movingFamily.patchMotion graph coordinate drive time).2|
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
    ContinuousOn allForcing (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.macroSourceState time drive) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * shape time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * allForcing time) volume 0 finish ∧
    (∀ time ∈ Icc 0 finish, prepared.finiteCoordinateForeignForcing drive time +
      prepared.physicalForeignSourceForcing drive time ≤ allForcing time) ∧
    weighted allForcing ≤ tolerance * weighted shape +
      8 * prepared.mixedSelectedFinerSourcePrefixBudget drive sharpIncoming sharpOutgoing extent coefficient
        entry initialDistance magnitude weight finish +
      (32 * followerConstant * rho / (changed.omega (drive.val + 1) * changed.location (drive.val + 1) ^ 4)) *
        prepared.mixedFollowerSourcePrefixBudget drive commonIncoming commonOutgoing extent coefficient
          entry initialDistance magnitude weight finish := by
  obtain ⟨closedThreshold, closedPositive, closedEighth, closedCap, closedCapPositive,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative, closedFactory⟩ :=
    exists_uniform_actual_mixed_follower_closed_weighted_forcing graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨sharpThreshold, sharpPositive, _, sharpCap, sharpCapPositive,
    sharpIncoming, sharpIncomingNonnegative, sharpOutgoing, sharpOutgoingNonnegative, sharpFactory⟩ :=
    exists_uniform_actual_mixed_selected_finer_original_prefix_budget
  obtain ⟨macroThreshold, macroPositive, _, macroCap, macroCapPositive, macroFactory⟩ :=
    exists_uniform_actual_macro_state_shape_arbitrary_weight_response graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  let thresholdMax := min closedThreshold (min sharpThreshold macroThreshold)
  let rawCap := min closedCap (min sharpCap macroCap)
  have closedCapBound : rawCap ≤ closedCap := min_le_left _ _
  have sharpCapBound : rawCap ≤ sharpCap := (min_le_right _ _).trans (min_le_left _ _)
  have macroCapBound : rawCap ≤ macroCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨thresholdMax, lt_min closedPositive (lt_min sharpPositive macroPositive), (min_le_left _ _).trans closedEighth,
    rawCap, lt_min closedCapPositive (lt_min sharpCapPositive macroCapPositive), commonIncoming, commonIncomingNonnegative,
    commonOutgoing, commonOutgoingNonnegative, sharpIncoming, sharpIncomingNonnegative, sharpOutgoing, sharpOutgoingNonnegative, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨closedRadius, closedRadiusPositive, closedQuarter, followerConstant, followerOne, ratioMin, ratioMinBound,
    closedRoot, closedEight, closedResponses⟩ := closedFactory factor factorPositive factorSmall
  obtain ⟨macroRadius, macroRadiusPositive, _, macroConstant, macroOne, macroRoot, _, macros⟩ :=
    macroFactory factor factorPositive factorSmall
  let radius := min closedRadius macroRadius
  let rootMin := max closedRoot macroRoot
  refine ⟨radius, lt_min closedRadiusPositive macroRadiusPositive, (min_le_left _ _).trans closedQuarter,
    followerConstant, followerOne, ratioMin, ratioMinBound, rootMin, closedEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive extent extentOne referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant tolerance boundaryOne tolerancePositive
  have ratioBound : 2 ≤ scales.ratio := ((le_max_left _ _).trans ratioMinBound).trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans
    (closedEight.trans ((le_max_left _ _).trans rootLarge))
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  let small := min (tolerance / (16 * macroConstant)) (1 / (16 * macroConstant))
  have smallPositive : 0 < small := lt_min (div_pos tolerancePositive (by positivity)) (by positivity)
  filter_upwards [closedResponses scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioLarge alphaPositive
      extent extentOne referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans (min_le_left _ _))
      orbit sectionTime boundaryConstant (tolerance / 4) boundaryOne (by positivity),
    sharpFactory extent extentOne small smallPositive scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans ((min_le_right _ _).trans (min_le_left _ _)))
      orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    macros scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans ((min_le_right _ _).trans (min_le_right _ _))) referenceNonnegative boundaryOne,
    eventually_ge_atTop (1 : ℝ)] with frequency closedResponse sharpResponse macroResponse frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path drive nonterminal terminal terminalNonnegative terminalBound
    entry initialDistance direction
  dsimp only
  intro entries extents coefficient coefficientPositive magnitude profiles finish finishInside radialSmall targetSmall followerSmall
    weight omegaWeight sourceRates
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (drive.val + 1)
  let location := changed.location (drive.val + 1)
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let allForcing := prepared.selectedForeignForcing (Finset.univ.erase drive) drive
  let finerForcing := prepared.selectedForeignForcing
    (Finset.univ.filter (fun source : Fin count => drive.val < source.val ∧ source ≠ drive)) drive
  let shape := fun time =>
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate drive time).1 -
      (referenceStraightenedShape prepared.referenceWitness.trajectory.movingFamily.patchMotion graph coordinate drive time).1| +
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate drive time).2 -
      (referenceStraightenedShape prepared.referenceWitness.trajectory.movingFamily.patchMotion graph coordinate drive time).2|
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  let common := prepared.mixedFollowerSourcePrefixBudget drive commonIncoming commonOutgoing extent coefficient
    entry initialDistance magnitude weight finish
  let sharp := prepared.mixedSelectedFinerSourcePrefixBudget drive sharpIncoming sharpOutgoing extent coefficient
    entry initialDistance magnitude weight finish
  have macroInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have selectedInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have commonInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).mixedFollowerSourcePrefixBudget = prepared.mixedFollowerSourcePrefixBudget := rfl
  have sharpInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).mixedSelectedFinerSourcePrefixBudget = prepared.mixedSelectedFinerSourcePrefixBudget := rfl
  have coordinateInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateForeignForcing = prepared.finiteCoordinateForeignForcing := rfl
  have physicalInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).physicalForeignSourceForcing = prepared.physicalForeignSourceForcing := rfl
  have closedData := closedResponse count phase dipoleAngle (prepared.enlargeCap closedCapBound) path drive nonterminal terminal
    terminalNonnegative terminalBound entry initialDistance direction entries extents coefficient coefficientPositive magnitude
    (by simpa only [rawInvariant] using profiles) finish finishInside radialSmall
    (fun time inside => (targetSmall time inside).trans (min_le_left _ _))
    (fun receiver below time inside => (followerSmall receiver below time inside).trans (min_le_left _ _)) weight omegaWeight sourceRates
  dsimp only at closedData
  simp only [macroInvariant, selectedInvariant, commonInvariant, coordinateInvariant, physicalInvariant] at closedData
  obtain ⟨allContinuous, _, _, macroI, shapeI, allI, _, _, literalBound, closedBound⟩ := closedData
  have sharpData := sharpResponse count phase dipoleAngle (prepared.enlargeCap sharpCapBound) path drive terminal terminalNonnegative
    terminalBound entry initialDistance direction entries extents coefficient coefficientPositive magnitude
    (by simpa only [rawInvariant] using profiles) finish finishInside weight (by
      exact (zero_lt_one.trans_le (frequencyOne.trans (changed.omega_ge_frequency
        (zero_lt_one.trans_le frequencyOne) (by linarith only [ratioBound]) _))).trans_le omegaWeight) sourceRates
  dsimp only at sharpData
  simp only [macroInvariant, selectedInvariant, sharpInvariant] at sharpData
  have sharpBound := sharpData.2.2.2.2
  have macroData := macroResponse count phase dipoleAngle (prepared.enlargeCap macroCapBound) path drive nonterminal finish
    finishInside.1 (finishInside.2.trans terminalBound) radialSmall
    (fun time inside => (targetSmall time inside).trans (min_le_right _ _)) weight omegaWeight
  dsimp only at macroData
  simp only [macroInvariant, selectedInvariant] at macroData
  have macroBound := macroData.2.2.2
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency
    (zero_lt_one.trans_le frequencyOne) (by linarith only [ratioBound]) _)
  have weightOne : 1 ≤ weight := omegaOne.trans omegaWeight
  have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
  have locationPositive : 0 < location := changed.location_pos _
  have smallMacro : 4 * small * macroConstant ≤ 1 / 4 := by
    calc
      _ = small * (4 * macroConstant) := by ring
      _ ≤ (1 / (16 * macroConstant)) * (4 * macroConstant) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = 1 / 4 := by (field_simp; ring)
  have smallShape : 4 * small * macroConstant ≤ tolerance / 4 := by
    calc
      _ = small * (4 * macroConstant) := by ring
      _ ≤ (tolerance / (16 * macroConstant)) * (4 * macroConstant) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = tolerance / 4 := by (field_simp; ring)
  have feedbackQuarter : 4 * small * (macroConstant / weight) ≤ 1 / 4 := by
    calc
      _ = (4 * small * macroConstant) / weight := by ring
      _ ≤ (1 / 4 : ℝ) / weight := div_le_div_of_nonneg_right smallMacro weightPositive.le
      _ ≤ 1 / 4 := div_le_self (by norm_num) weightOne
  have shapeBound : 2 * (tolerance / 4 + 4 * small * macroConstant) ≤ tolerance := by linarith only [smallShape]
  have allNonnegative : 0 ≤ weighted allForcing := intervalIntegral.integral_nonneg finishInside.1
    (fun time _ => mul_nonneg (Real.exp_pos _).le (by
      dsimp only [allForcing, CascadeSourcePreparedPair.selectedForeignForcing,
        CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm]
      positivity))
  have shapeNonnegative : 0 ≤ weighted shape := intervalIntegral.integral_nonneg finishInside.1
    (fun time _ => mul_nonneg (Real.exp_pos _).le (add_nonneg (abs_nonneg _) (abs_nonneg _)))
  change weighted allForcing ≤ (tolerance / 4) * weighted shape + 4 * weighted finerForcing +
    (16 * followerConstant * rho / (omega * location ^ 4)) * common at closedBound
  change weighted finerForcing ≤ sharp + small * weighted (fun time => prepared.macroSourceState time drive) at sharpBound
  have scalar := all_foreign_feedback_scalar allNonnegative shapeNonnegative smallPositive.le closedBound sharpBound macroBound
    (feedbackQuarter.trans (by norm_num)) shapeBound
  refine ⟨allContinuous, macroI, shapeI, allI, literalBound, ?_⟩
  change weighted allForcing ≤ tolerance * weighted shape + 8 * sharp +
    (32 * followerConstant * rho / (omega * location ^ 4)) * common
  (convert scalar using 1; ring)

end EulerNonuniqueness.Paper

