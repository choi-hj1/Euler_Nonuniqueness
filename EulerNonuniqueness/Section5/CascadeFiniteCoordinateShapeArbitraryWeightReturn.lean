import EulerNonuniqueness.Section5.CascadeStrongNeutralLocalForeignArbitraryWeightReturn
import EulerNonuniqueness.Section5.CascadeCenterLocalForeignWeightedReturn
import EulerNonuniqueness.Section5.CascadeFiniteCoordinateLocalForeignHistory
import EulerNonuniqueness.Section5.CascadePhysicalForeignForcingContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem finite_coordinate_weighted_scalar
    {bound weight omega centered raw moment velocity dilation phase translation shape forcing : ℝ}
    (boundOne : 1 ≤ bound) (weightOne : 1 ≤ weight) (omegaWeight : omega ≤ weight)
    (centeredNonnegative : 0 ≤ centered) (rawNonnegative : 0 ≤ raw) (momentNonnegative : 0 ≤ moment)
    (velocityNonnegative : 0 ≤ velocity) (shapeNonnegative : 0 ≤ shape) (forcingNonnegative : 0 ≤ forcing)
    (neutralBound : centered ≤ bound * shape + (bound / weight) * forcing)
    (rawBound : weight * raw ≤ bound * omega * centered + bound * forcing)
    (momentBound : weight * moment ≤ bound * (centered + raw + forcing))
    (velocityBound : velocity ≤ moment + (1 + 2 * bound) * centered + bound * raw + bound * forcing)
    (dilationBound : weight * dilation ≤ velocity)
    (phaseBound : weight * phase ≤ 2 * omega * (velocity / weight) + omega * shape +
      (moment + centered + shape) + bound * (centered + raw) + bound * forcing)
    (translationBound : weight * translation ≤ moment + centered + forcing + bound * (centered + raw) + bound * forcing) :
    let constant := 3 + (5 + 17 * bound) * (1 + bound) ^ 2
    shape + dilation + phase + moment + translation ≤ constant * shape + (constant / weight) * forcing := by
  have boundNonnegative : 0 ≤ bound := zero_le_one.trans boundOne
  have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
  let source := forcing / weight
  let total := centered + raw + source
  have sourceNonnegative : 0 ≤ source := div_nonneg forcingNonnegative weightPositive.le
  have totalNonnegative : 0 ≤ total := by dsimp only [total]; positivity
  have sourceIdentity : weight * source = forcing := by dsimp only [source]; field_simp
  have rawUpper : raw ≤ bound * centered + bound * source := by
    apply (mul_le_mul_left weightPositive).mp
    have localTerm := mul_le_mul_of_nonneg_left omegaWeight (mul_nonneg boundNonnegative centeredNonnegative)
    have identity : weight * (bound * centered + bound * source) = bound * weight * centered + bound * forcing := by
      rw [mul_add, show weight * (bound * source) = bound * (weight * source) by ring, sourceIdentity]; ring
    rw [identity]
    nlinarith only [rawBound, localTerm]
  have momentUpper : moment ≤ bound * total := by
    apply (mul_le_mul_left weightPositive).mp
    have localTerm := mul_le_mul_of_nonneg_right weightOne (show 0 ≤ bound * (centered + raw) by positivity)
    apply momentBound.trans
    have identity : weight * (bound * total) = weight * (bound * (centered + raw)) + bound * forcing := by
      dsimp only [total]
      rw [mul_add, mul_add]
      nlinarith only [congrArg (fun value : ℝ => bound * value) sourceIdentity]
    rw [identity]
    nlinarith only [localTerm]
  change moment ≤ bound * (centered + raw + source) at momentUpper
  have velocityUpper : velocity / weight ≤ (1 + 4 * bound) * total := by
    apply (div_le_iff₀ weightPositive).mpr
    have localTerm := mul_le_mul_of_nonneg_right weightOne
      (show 0 ≤ moment + (1 + 2 * bound) * centered + bound * raw by positivity)
    have localBound : moment + (1 + 2 * bound) * centered + bound * raw + bound * source ≤
        (1 + 4 * bound) * total := by dsimp only [total]; nlinarith only [momentUpper, centeredNonnegative, rawNonnegative, sourceNonnegative, mul_nonneg boundNonnegative centeredNonnegative, mul_nonneg boundNonnegative rawNonnegative, mul_nonneg boundNonnegative sourceNonnegative]
    have scaled := mul_le_mul_of_nonneg_right localBound weightPositive.le
    have identity : weight * (bound * source) = bound * forcing := by nlinarith only [congrArg (fun value : ℝ => bound * value) sourceIdentity]
    nlinarith only [velocityBound, localTerm, scaled, identity]
  change velocity / weight ≤ (1 + 4 * bound) * (centered + raw + source) at velocityUpper
  have dilationUpper : dilation ≤ (1 + 4 * bound) * total :=
    ((le_div_iff₀ weightPositive).mpr (by simpa only [mul_comm] using dilationBound)).trans velocityUpper
  have phaseUpper : phase ≤ 2 * shape + (3 + 10 * bound) * total := by
    apply (mul_le_mul_left weightPositive).mp
    have velocityScaled := mul_le_mul_of_nonneg_right omegaWeight (show 0 ≤ velocity / weight by positivity)
    have shapeScaled := mul_le_mul_of_nonneg_right omegaWeight shapeNonnegative
    have localTerm := mul_le_mul_of_nonneg_right weightOne
      (show 0 ≤ moment + centered + shape + bound * (centered + raw) by positivity)
    have localBound : 2 * (velocity / weight) + 2 * shape + moment + centered + bound * (centered + raw) + bound * source ≤
        2 * shape + (3 + 10 * bound) * total := by
      dsimp only [total]
      nlinarith only [velocityUpper, momentUpper, centeredNonnegative, rawNonnegative, sourceNonnegative,
        mul_nonneg boundNonnegative sourceNonnegative]
    have scaled := mul_le_mul_of_nonneg_right localBound weightPositive.le
    have identity : weight * (bound * source) = bound * forcing := by nlinarith only [congrArg (fun value : ℝ => bound * value) sourceIdentity]
    have scaledVelocity := mul_le_mul_of_nonneg_left velocityScaled (by norm_num : (0 : ℝ) ≤ 2)
    have enlarged : weight * phase ≤ 2 * (weight * (velocity / weight)) + weight * shape +
        weight * (moment + centered + shape + bound * (centered + raw)) + bound * forcing := by
      nlinarith only [phaseBound, scaledVelocity, shapeScaled, localTerm]
    apply enlarged.trans
    calc
      _ = (2 * (velocity / weight) + 2 * shape + moment + centered + bound * (centered + raw) + bound * source) * weight := by
        rw [← identity]; ring
      _ ≤ _ := scaled
      _ = _ := mul_comm _ _
  have translationUpper : translation ≤ (1 + 2 * bound) * total := by
    apply (mul_le_mul_left weightPositive).mp
    have localTerm := mul_le_mul_of_nonneg_right weightOne
      (show 0 ≤ moment + centered + bound * (centered + raw) by positivity)
    have localBound : moment + centered + bound * (centered + raw) + (1 + bound) * source ≤
        (1 + 2 * bound) * total := by
      dsimp only [total]
      nlinarith only [momentUpper, rawNonnegative]
    have scaled := mul_le_mul_of_nonneg_right localBound weightPositive.le
    have identity : weight * ((1 + bound) * source) = forcing + bound * forcing := by
      nlinarith only [sourceIdentity, congrArg (fun value : ℝ => bound * value) sourceIdentity]
    nlinarith only [translationBound, localTerm, scaled, identity]
  have neutralUpper : centered ≤ bound * shape + bound * source := by
    convert neutralBound using 1
    dsimp only [source]
    ring
  have totalUpper : total ≤ bound * (1 + bound) * shape + (1 + bound) ^ 2 * source := by
    have first := mul_le_mul_of_nonneg_left neutralUpper (show 0 ≤ 1 + bound by positivity)
    dsimp only [total]
    nlinarith only [rawUpper, first]
  have combined : shape + dilation + phase + moment + translation ≤ 3 * shape + (5 + 17 * bound) * total := by
    change moment ≤ bound * total at momentUpper
    linarith only [dilationUpper, phaseUpper, momentUpper, translationUpper]
  have substituted := combined.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left totalUpper (show 0 ≤ 5 + 17 * bound by positivity)) _)
  have coefficient : bound * (1 + bound) ≤ (1 + bound) ^ 2 := by nlinarith only [boundNonnegative]
  have shapeBound := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right coefficient shapeNonnegative)
    (show 0 ≤ 5 + 17 * bound by positivity)
  have extra := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) sourceNonnegative
  dsimp only
  have result : shape + dilation + phase + moment + translation ≤
      (3 + (5 + 17 * bound) * (1 + bound) ^ 2) * shape +
        (3 + (5 + 17 * bound) * (1 + bound) ^ 2) * source := by
    nlinarith only [substituted, shapeBound, extra]
  convert result using 1
  dsimp only [source]
  ring

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_finite_coordinate_shape_arbitrary_weight_return
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha → ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant boundaryConstant : ℝ},
    threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
    (∀ side, suppliedLift side 0 = phase (index.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
    ∀ weight : ℝ, ({scales with frequency := frequency} : Scales).omega (index.val + 1) ≤ weight →
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let shape := fun time =>
      |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
      |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2|
    let forcing := fun time => prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.finiteCoordinateSize graph coordinate suppliedLift index time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * shape time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.finiteCoordinateSize graph coordinate suppliedLift index time) ≤
      constant * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * shape time) +
      (constant / weight) * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time := by
  obtain ⟨neutralThreshold, neutralThresholdPositive, neutralThresholdEighth, neutralCap, neutralPositive, neutrals⟩ :=
    exists_uniform_actual_strong_neutral_local_foreign_arbitrary_weight_return graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨phaseThreshold, phaseThresholdPositive, _, phaseCap, phasePositive, phases⟩ :=
    exists_uniform_actual_cascade_corrected_phase_local_foreign_arbitrary_weight_return graphAnalytic graphZero graphDerivative coordinateSmooth coordinateZero coordinateDerivative
  obtain ⟨momentCap, momentPositive, moments⟩ := exists_uniform_actual_firstMoment_local_foreign_arbitrary_weight_return
  obtain ⟨rawSourceCap, rawSourcePositive, raws⟩ := exists_uniform_actual_raw_source_weighted_local_foreign_return
  obtain ⟨dilationCap, dilationPositive, dilations⟩ := exists_uniform_actual_prehit_dilation_local_foreign_arbitrary_weight_return
  obtain ⟨centerCap, centerPositive, centers⟩ := exists_uniform_actual_center_local_foreign_weighted_return
  let thresholdMax := min neutralThreshold phaseThreshold
  let rawCap := min neutralCap (min phaseCap (min momentCap (min rawSourceCap (min dilationCap centerCap))))
  have capPositive : 0 < rawCap := lt_min neutralPositive (lt_min phasePositive
    (lt_min momentPositive (lt_min rawSourcePositive (lt_min dilationPositive centerPositive))))
  have neutralCapBound : rawCap ≤ neutralCap := min_le_left _ _
  have phaseCapBound : rawCap ≤ phaseCap := (min_le_right _ _).trans (min_le_left _ _)
  have momentCapBound : rawCap ≤ momentCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have rawCapBound : rawCap ≤ rawSourceCap := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have dilationCapBound : rawCap ≤ dilationCap := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have centerCapBound : rawCap ≤ centerCap := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  refine ⟨thresholdMax, lt_min neutralThresholdPositive phaseThresholdPositive, (min_le_left _ _).trans neutralThresholdEighth,
    rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨neutralRadius, neutralRadiusPositive, neutralQuarter, neutralConstant, neutralNonnegative, neutralRoot, neutralEight, neutralFactory⟩ := neutrals factor factorPositive factorSmall
  obtain ⟨phaseConstant, phaseNonnegative, phaseFactory⟩ := phases factorPositive factorEighth
  obtain ⟨phaseRadius, phaseRadiusPositive, _, phaseParameters⟩ := phaseFactory 1 (by norm_num)
  obtain ⟨momentConstant, momentNonnegative, momentFactory⟩ := moments factorPositive factorEighth
  obtain ⟨rawConstant, rawNonnegative, rawRoot, rawEight, rawFactory⟩ := raws factor factorPositive factorOne
  obtain ⟨dilationConstant, dilationNonnegative, dilationFactory⟩ := dilations factorPositive factorSmall
  obtain ⟨centerConstant, centerNonnegative, centerFactory⟩ := centers factorPositive factorSmall
  let bound := 1 + neutralConstant + rawConstant + 2 * momentConstant + dilationConstant + phaseConstant + centerConstant
  have boundOne : 1 ≤ bound := by dsimp only [bound]; linarith
  have boundNonnegative : 0 ≤ bound := zero_le_one.trans boundOne
  have neutralBelow : neutralConstant ≤ bound := by dsimp only [bound]; linarith
  have rawBelow : rawConstant ≤ bound := by dsimp only [bound]; linarith
  have momentBelow : 2 * momentConstant ≤ bound := by dsimp only [bound]; linarith
  have dilationBelow : dilationConstant ≤ bound := by dsimp only [bound]; linarith
  have phaseBelow : phaseConstant ≤ bound := by dsimp only [bound]; linarith
  have centerBelow : centerConstant ≤ bound := by dsimp only [bound]; linarith
  let constant := 3 + (5 + 17 * bound) * (1 + bound) ^ 2
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ (5 + 17 * bound) * (1 + bound) ^ 2 := by positivity
    dsimp only [constant]
    linarith only [nonnegative]
  let radius := min neutralRadius phaseRadius
  let rootMin := max neutralRoot rawRoot
  have rootEight : 8 ≤ rootMin := neutralEight.trans (le_max_left _ _)
  refine ⟨radius, lt_min neutralRadiusPositive phaseRadiusPositive, (min_le_left _ _).trans neutralQuarter,
    constant, constantOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive orbit sectionTime threshold referenceConstant boundaryConstant thresholdBound referenceNonnegative boundaryOne
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans ((min_le_left _ _).trans neutralThresholdEighth)
  filter_upwards [neutralFactory scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans (min_le_left _ _)) referenceNonnegative boundaryOne,
    phaseParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      (thresholdBound.trans (min_le_right _ _)) referenceNonnegative,
    momentFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    rawFactory scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
      thresholdSmall referenceNonnegative boundaryOne orbit sectionTime,
    dilationFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative (by norm_num : (0 : ℝ) < 1),
    centerFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative (by norm_num : (0 : ℝ) < 1),
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    scales.eventually_cascade_relative_leading_strain_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)]
    with frequency neutralEstimate phaseEstimate momentEstimate rawEstimate dilationEstimate centerEstimate coherence leadingContinuity lengths strainSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound small
    suppliedLift suppliedContinuous suppliedInitial suppliedPolar weight omegaWeight
  dsimp only
  by_cases finishZero : finish = 0
  · subst finish
    refine ⟨IntervalIntegrable.refl, IntervalIntegrable.refl, IntervalIntegrable.refl, ?_⟩
    simp only [intervalIntegral.integral_same, mul_zero, add_zero, le_refl]
  have finishPositive : 0 < finish := lt_of_le_of_ne finishNonnegative (Ne.symm finishZero)
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let omega := changed.omega (index.val + 1)
  let location := changed.location (index.val + 1)
  let length := changed.length (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let ratio := length / location
  let macroRadius := factor / 39321600 * location
  let ownRadius := factor / 39321600 * length
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  let shape := fun time =>
    |(referenceStraightenedShape first.patchMotion graph coordinate index time).1 - (referenceStraightenedShape second.patchMotion graph coordinate index time).1| +
    |(referenceStraightenedShape first.patchMotion graph coordinate index time).2 - (referenceStraightenedShape second.patchMotion graph coordinate index time).2|
  let centered := fun time => prepared.rawSourceCenteredState time index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let moment := fun time => ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖
  let velocity := fun time => |relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index time|
  let dilation := fun time => |(diagonalDifference first.patchMotion time index - diagonalDifference second.patchMotion time index) / length ^ 2|
  let relativePhase := fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|
  let translation := fun time => ‖quadrupoleCenter first.patchMotion time index - quadrupoleCenter second.patchMotion time index‖ / location
  let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first.patchMotion index time macroRadius power - quadrupoleExteriorCoefficient changed second.patchMotion index time macroRadius power‖
  let foreign := fun receiverRadius patch time => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index) (fun current => patchCentroid first.patchMotion current index patch) receiverRadius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index) (fun current => patchCentroid second.patchMotion current index patch) receiverRadius (power + 1) time‖
  let external := fun patch time => ‖biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch) -
    biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch)‖
  let leading := fun time => ‖quadrupoleRelativeLeadingStrain changed first.patchMotion second.patchMotion time index‖
  let forcing := fun time => prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time
  have centerCapInvariant {largerCap : ℝ} (capBound : rawCap ≤ largerCap) :
      (prepared.enlargeCap capBound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawCapInvariant {largerCap : ℝ} (capBound : rawCap ≤ largerCap) :
      (prepared.enlargeCap capBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have referenceCapInvariant {largerCap : ℝ} (capBound : rawCap ≤ largerCap) : (prepared.enlargeCap capBound).reference = prepared.reference := rfl
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have weightOne : 1 ≤ weight := omegaOne.trans omegaWeight
  have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
  have locationPositive : 0 < location := changed.location_pos _
  have lengthPositive : 0 < length := changed.length_pos _
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have omegaEpsilonIdentity : omega * epsilon = 2 / (changed.amplitude * omega ^ 2) := by
    dsimp only [epsilon, length]
    rw [changed.radius_sq amplitudePositive frequencyPositive ratioPositive]
    field_simp [(changed.length_pos (index.val + 1)).ne', amplitudePositive.ne', omegaPositive.ne']
    ring
  have amplitudeTwo : 2 ≤ changed.amplitude := by
    calc
      2 ≤ (8 : ℝ) ^ 3 := by norm_num
      _ ≤ scaleRoot ^ 3 := pow_le_pow_left₀ (by norm_num) (rootEight.trans rootLarge) 3
      _ = changed.amplitude := amplitudeIdentity.symm
  have omegaEpsilonOne : omega * epsilon ≤ 1 := by
    rw [omegaEpsilonIdentity]
    apply (div_le_one (by positivity : 0 < changed.amplitude * omega ^ 2)).mpr
    have lower := mul_le_mul_of_nonneg_left (one_le_pow₀ omegaOne (n := 2)) amplitudePositive.le
    exact amplitudeTwo.trans (by simpa only [mul_one] using lower)
  have epsilonOne : epsilon ≤ 1 := (le_mul_of_one_le_left epsilonNonnegative omegaOne).trans omegaEpsilonOne
  have ratioNonnegative : 0 ≤ ratio := div_nonneg lengthPositive.le locationPositive.le
  have ratioOne : ratio ≤ 1 := (div_le_one locationPositive).mpr (by simpa only [one_mul] using (lengths (index.val + 1)).le)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source => div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have radialSmall (time : ℝ) (inside : time ∈ Icc 0 finish) : |radialShape first.patchMotion time index| ≤ 1 / 2 := by
    have identity : radialShape first.patchMotion time index = unstableShape first.patchMotion time index + stableShape first.patchMotion time index := by
      unfold unstableShape stableShape
      ring
    rw [identity]
    exact (abs_add_le _ _).trans ((small time inside).trans ((min_le_left _ _).trans (neutralQuarter.trans (by norm_num))))
  have neutralData := neutralEstimate count phase dipoleAngle (prepared.enlargeCap neutralCapBound) path index nonterminal finish finishNonnegative finishBound radialSmall
    (fun time inside => (small time inside).trans (min_le_left _ _)) suppliedLift suppliedContinuous suppliedInitial suppliedPolar weight omegaWeight
  have momentData := momentEstimate count phase dipoleAngle (prepared.enlargeCap momentCapBound) path index nonterminal finish finishNonnegative finishBound radialSmall weight omegaWeight
  have rawData := rawEstimate count phase dipoleAngle (prepared.enlargeCap rawCapBound) path index finish finishNonnegative finishBound weight omegaWeight
  have dilationData := dilationEstimate count phase dipoleAngle (prepared.enlargeCap dilationCapBound) path index nonterminal finish finishNonnegative finishBound radialSmall weight omegaWeight
  have centerData := centerEstimate count phase dipoleAngle (prepared.enlargeCap centerCapBound) path index nonterminal finish finishNonnegative finishBound radialSmall weight weightPositive
  obtain ⟨lift, liftContinuous, polar, allWeights⟩ := phaseEstimate count phase dipoleAngle (prepared.enlargeCap phaseCapBound) path index nonterminal finish finishPositive finishBound radialSmall
    (fun time inside => (small time inside).trans (min_le_right _ _))
  have phaseData := allWeights weight omegaWeight
  dsimp only at neutralData momentData rawData dilationData centerData phaseData
  simp only [centerCapInvariant, rawCapInvariant, referenceCapInvariant, prepared.referenceIdentity] at neutralData momentData rawData dilationData centerData phaseData
  have liftEquality := coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans ((min_le_left _ _).trans neutralQuarter))
    lift suppliedLift (fun side => (liftContinuous side).1.continuousOn) suppliedContinuous
    (fun side => (liftContinuous side).2.trans (suppliedInitial side).symm) polar suppliedPolar
  have phaseEquality : EqOn (fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|) relativePhase (Icc 0 finish) :=
    fun time inside => congrArg abs (liftEquality.2.1 (phaseCorrection 1 graph) inside)
  have phaseIntegralEquality : weighted (fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|) = weighted relativePhase := by
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le finishNonnegative] at inside
    exact congrArg (fun value : ℝ => Real.exp (-weight * time) * value) (phaseEquality inside)
  have differenceI : IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish := momentData.1
  have macroPatchI (patch : Fin 4) : IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign macroRadius patch time) volume 0 finish := momentData.2.1 patch
  have ownPatchI (patch : Fin 4) : IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign ownRadius patch time) volume 0 finish := centerData.2.2.1 patch
  have physicalPatchI (patch : Fin 4) : IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign (changed.radius (index.val + 1)) patch time) volume 0 finish := by
    simpa only [foreign, first, second, norm_sub_rev] using rawData.1 patch
  have externalI (patch : Fin 4) : IntervalIntegrable (fun time => Real.exp (-weight * time) * external patch time) volume 0 finish := centerData.2.1 patch
  have momentI : IntervalIntegrable (fun time => Real.exp (-weight * time) * moment time) volume 0 finish := momentData.2.2.2.2.1
  have dilationI : IntervalIntegrable (fun time => Real.exp (-weight * time) * dilation time) volume 0 finish := dilationData.1
  have shapeI : IntervalIntegrable (fun time => Real.exp (-weight * time) * shape time) volume 0 finish := phaseData.2.2.1
  have phaseI : IntervalIntegrable (fun time => Real.exp (-weight * time) * relativePhase time) volume 0 finish := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le finishNonnegative).mpr
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le finishNonnegative).mp phaseData.1).congr_fun
      (fun time inside => congrArg (fun value : ℝ => Real.exp (-weight * time) * value) (phaseEquality inside)) measurableSet_Icc
  have translationI : IntervalIntegrable (fun time => Real.exp (-weight * time) * translation time) volume 0 finish := centerData.1
  have leadingContinuous : ContinuousOn leading (Icc 0 finish) := by
    have actual := leadingContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index
    rw [prepared.referenceIdentity] at actual
    exact actual.norm.mono (Icc_subset_Icc le_rfl finishBound)
  have leadingI := ((by fun_prop : Continuous (fun time : ℝ => Real.exp (-weight * time))).continuousOn.mul leadingContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have sumI (values : Fin 4 → ℝ → ℝ) (integrable : ∀ patch, IntervalIntegrable (fun time => Real.exp (-weight * time) * values patch time) volume 0 finish) :
      IntervalIntegrable (fun time => Real.exp (-weight * time) * ∑ patch : Fin 4, values patch time) volume 0 finish := by
    simpa only [Finset.mul_sum] using (IntervalIntegrable.sum Finset.univ (fun patch _ => integrable patch))
  have sumIdentity (values : Fin 4 → ℝ → ℝ) (integrable : ∀ patch, IntervalIntegrable (fun time => Real.exp (-weight * time) * values patch time) volume 0 finish) :
      weighted (fun time => ∑ patch : Fin 4, values patch time) = ∑ patch : Fin 4, weighted (values patch) := by
    dsimp only [weighted]
    simp_rw [Finset.mul_sum]
    exact intervalIntegral.integral_finset_sum (fun patch _ => integrable patch)
  let core := fun time => difference time + epsilon * (∑ patch : Fin 4, foreign macroRadius patch time) +
    epsilon * (∑ patch : Fin 4, foreign ownRadius patch time) + (∑ patch : Fin 4, foreign (changed.radius (index.val + 1)) patch time) +
    (∑ patch : Fin 4, external patch time) / (4 * location)
  have expandedCoreI := (((differenceI.add ((sumI _ macroPatchI).const_mul epsilon)).add ((sumI _ ownPatchI).const_mul epsilon)).add
    (sumI _ physicalPatchI)).add ((sumI _ externalI).div_const (4 * location))
  have coreI : IntervalIntegrable (fun time => Real.exp (-weight * time) * core time) volume 0 finish := by
    convert expandedCoreI using 1
    funext time
    dsimp only [core]
    ring
  have forcingIdentity (time : ℝ) : forcing time = leading time + core time := by
    dsimp only [forcing, leading, core, CascadeSourcePreparedPair.finiteCoordinateForeignForcing,
      CascadeSourcePreparedPair.physicalForeignSourceForcing, first, second, difference, foreign, external, macroRadius, ownRadius, epsilon, location, length]
    ring
  have forcingI : IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 finish := by
    convert leadingI.add coreI using 1
    funext time
    rw [forcingIdentity, mul_add]
  have coreIdentity : weighted core = weighted difference + epsilon * (∑ patch : Fin 4, weighted (foreign macroRadius patch)) +
      epsilon * (∑ patch : Fin 4, weighted (foreign ownRadius patch)) + (∑ patch : Fin 4, weighted (foreign (changed.radius (index.val + 1)) patch)) +
      (∑ patch : Fin 4, weighted (external patch)) / (4 * location) := by
    have identity : (fun time => Real.exp (-weight * time) * core time) = fun time =>
        (((Real.exp (-weight * time) * difference time + epsilon * (Real.exp (-weight * time) * ∑ patch, foreign macroRadius patch time)) +
        epsilon * (Real.exp (-weight * time) * ∑ patch, foreign ownRadius patch time)) + Real.exp (-weight * time) * ∑ patch, foreign (changed.radius (index.val + 1)) patch time) +
        (Real.exp (-weight * time) * ∑ patch, external patch time) / (4 * location) := by funext time; dsimp only [core]; ring
    dsimp only [weighted]
    rw [identity, intervalIntegral.integral_add (((differenceI.add ((sumI _ macroPatchI).const_mul epsilon)).add ((sumI _ ownPatchI).const_mul epsilon)).add (sumI _ physicalPatchI)) ((sumI _ externalI).div_const (4 * location)),
      intervalIntegral.integral_add ((differenceI.add ((sumI _ macroPatchI).const_mul epsilon)).add ((sumI _ ownPatchI).const_mul epsilon)) (sumI _ physicalPatchI),
      intervalIntegral.integral_add (differenceI.add ((sumI _ macroPatchI).const_mul epsilon)) ((sumI _ ownPatchI).const_mul epsilon),
      intervalIntegral.integral_add differenceI ((sumI _ macroPatchI).const_mul epsilon), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
    change weighted difference + epsilon * weighted (fun time => ∑ patch, foreign macroRadius patch time) + epsilon * weighted (fun time => ∑ patch, foreign ownRadius patch time) +
      weighted (fun time => ∑ patch, foreign (changed.radius (index.val + 1)) patch time) + weighted (fun time => ∑ patch, external patch time) / (4 * location) = _
    rw [sumIdentity _ macroPatchI, sumIdentity _ ownPatchI, sumIdentity _ physicalPatchI, sumIdentity _ externalI]
  have coreComparison := intervalIntegral.integral_mono_on finishNonnegative coreI forcingI (fun time _ =>
    mul_le_mul_of_nonneg_left (show core time ≤ forcing time by rw [forcingIdentity]; exact le_add_of_nonneg_left (norm_nonneg _)) (Real.exp_pos _).le)
  change weighted core ≤ weighted forcing at coreComparison
  rw [coreIdentity] at coreComparison
  have weightedNonnegative (function : ℝ → ℝ) (nonnegative : ∀ time, 0 ≤ function time) : 0 ≤ weighted function :=
    intervalIntegral.integral_nonneg_of_forall finishNonnegative (fun time => mul_nonneg (Real.exp_pos _).le (nonnegative time))
  have centeredNonnegative : 0 ≤ weighted centered := weightedNonnegative _ (fun _ => div_nonneg (norm_nonneg _) lengthPositive.le)
  have rawValueNonnegative : 0 ≤ weighted raw := weightedNonnegative _ (fun time => by dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity)
  have momentValueNonnegative : 0 ≤ weighted moment := weightedNonnegative _ (fun _ => norm_nonneg _)
  have velocityNonnegative : 0 ≤ weighted velocity := weightedNonnegative _ (fun _ => abs_nonneg _)
  have shapeNonnegative : 0 ≤ weighted shape := weightedNonnegative _ (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have blockNonnegative : 0 ≤ weighted difference := weightedNonnegative _ (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
  have patchNonnegative (receiverRadius : ℝ) : 0 ≤ ∑ patch : Fin 4, weighted (foreign receiverRadius patch) := Finset.sum_nonneg (fun patch _ =>
    weightedNonnegative _ (fun _ => tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _))))
  have externalNonnegative : 0 ≤ (∑ patch : Fin 4, weighted (external patch)) / (4 * location) := div_nonneg
    (Finset.sum_nonneg (fun patch _ => weightedNonnegative _ (fun _ => norm_nonneg _))) (by positivity)
  have macroPatchNonnegative := patchNonnegative macroRadius
  have ownPatchNonnegative := patchNonnegative ownRadius
  have physicalPatchNonnegative := patchNonnegative (changed.radius (index.val + 1))
  have forcingNonnegative : 0 ≤ weighted forcing :=
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg blockNonnegative
      (mul_nonneg epsilonNonnegative macroPatchNonnegative)) (mul_nonneg epsilonNonnegative ownPatchNonnegative))
      physicalPatchNonnegative) externalNonnegative).trans coreComparison
  have physicalBound : (∑ patch : Fin 4, weighted (foreign (changed.radius (index.val + 1)) patch)) ≤ weighted forcing := by
    nlinarith only [coreComparison, blockNonnegative, externalNonnegative, mul_nonneg epsilonNonnegative (patchNonnegative macroRadius), mul_nonneg epsilonNonnegative (patchNonnegative ownRadius)]
  have macroBound : weighted difference + epsilon * (∑ patch : Fin 4, weighted (foreign macroRadius patch)) ≤ weighted forcing := by
    nlinarith only [coreComparison, externalNonnegative, patchNonnegative (changed.radius (index.val + 1)), mul_nonneg epsilonNonnegative (patchNonnegative ownRadius)]
  have ownBound : weighted difference + epsilon * (∑ patch : Fin 4, weighted (foreign ownRadius patch)) ≤ weighted forcing := by
    nlinarith only [coreComparison, externalNonnegative, patchNonnegative (changed.radius (index.val + 1)), mul_nonneg epsilonNonnegative (patchNonnegative macroRadius)]
  have externalBound : (∑ patch : Fin 4, weighted (external patch)) / (4 * location) ≤ weighted forcing := by
    nlinarith only [coreComparison, blockNonnegative, patchNonnegative (changed.radius (index.val + 1)), mul_nonneg epsilonNonnegative (patchNonnegative macroRadius), mul_nonneg epsilonNonnegative (patchNonnegative ownRadius)]
  have neutralForcing : weighted difference + epsilon * (∑ patch : Fin 4, weighted (foreign macroRadius patch)) + epsilon * (∑ patch : Fin 4, weighted (foreign ownRadius patch)) +
      epsilon * (∑ patch : Fin 4, weighted (foreign (changed.radius (index.val + 1)) patch)) ≤ weighted forcing := by
    have physical := mul_le_of_le_one_left (patchNonnegative (changed.radius (index.val + 1))) epsilonOne
    linarith only [coreComparison, physical, externalNonnegative]
  have neutralBound : weighted centered ≤ bound * weighted shape + (bound / weight) * weighted forcing := by
    exact neutralData.2.trans (add_le_add (mul_le_mul_of_nonneg_right neutralBelow shapeNonnegative)
      ((mul_le_mul_of_nonneg_left neutralForcing (div_nonneg neutralNonnegative weightPositive.le)).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right neutralBelow weightPositive.le) forcingNonnegative)))
  have rawBound : weight * weighted raw ≤ bound * omega * weighted centered + bound * weighted forcing := by
    have actual : weight * weighted raw ≤ rawConstant * omega * weighted centered + rawConstant * ∑ patch : Fin 4, weighted (foreign (changed.radius (index.val + 1)) patch) := by
      simpa only [weighted, raw, centered, foreign, omega, first, second, norm_sub_rev] using rawData.2.2
    exact actual.trans (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right rawBelow omegaPositive.le) centeredNonnegative)
      ((mul_le_mul_of_nonneg_left physicalBound rawNonnegative).trans (mul_le_mul_of_nonneg_right rawBelow forcingNonnegative)))
  have momentBound : weight * weighted moment ≤ bound * (weighted centered + weighted raw + weighted forcing) := by
    have actual : weight * weighted moment ≤ 2 * momentConstant * (changed.strain * weighted centered + weighted difference + epsilon * (changed.strain * weighted raw + ∑ patch : Fin 4, weighted (foreign macroRadius patch))) := momentData.2.2.2.2.2
    have first := mul_le_of_le_one_left centeredNonnegative strainSmall.le
    have second := mul_le_of_le_one_left rawValueNonnegative (show epsilon * changed.strain ≤ 1 from (mul_le_mul epsilonOne strainSmall.le strainNonnegative (by norm_num)).trans_eq (by ring))
    have upper : changed.strain * weighted centered + weighted difference + epsilon * (changed.strain * weighted raw + ∑ patch : Fin 4, weighted (foreign macroRadius patch)) ≤ weighted centered + weighted raw + weighted forcing := by nlinarith only [first, second, macroBound]
    exact actual.trans ((mul_le_mul_of_nonneg_left upper (by positivity : 0 ≤ 2 * momentConstant)).trans
      (mul_le_mul_of_nonneg_right momentBelow (by positivity)))
  have dilationFeedback : dilationConstant * omega * epsilon ≤ bound := by nlinarith only [mul_le_mul_of_nonneg_left omegaEpsilonOne dilationNonnegative, dilationBelow]
  have dilationStrain : dilationConstant * changed.strain ≤ bound := (mul_le_of_le_one_right dilationNonnegative strainSmall.le).trans dilationBelow
  have phaseFeedback : phaseConstant * omega * epsilon ≤ bound := by nlinarith only [mul_le_mul_of_nonneg_left omegaEpsilonOne phaseNonnegative, phaseBelow]
  have centerFeedback : centerConstant * omega * ratio * epsilon ≤ bound := by
    have first := mul_le_mul_of_nonneg_left ratioOne (show 0 ≤ centerConstant * (omega * epsilon) by positivity)
    nlinarith only [first, mul_le_mul_of_nonneg_left omegaEpsilonOne centerNonnegative, centerBelow]
  have sourceComparison (coefficient : ℝ) (nonnegative : 0 ≤ coefficient) (below : coefficient ≤ bound) :
      coefficient * weighted difference + coefficient * epsilon * (∑ patch : Fin 4, weighted (foreign ownRadius patch)) ≤ bound * weighted forcing := by
    have first := mul_le_mul_of_nonneg_left ownBound nonnegative
    have second := mul_le_mul_of_nonneg_right below forcingNonnegative
    nlinarith only [first, second]
  have velocityBound : weighted velocity ≤ weighted moment + (1 + 2 * bound) * weighted centered + bound * weighted raw + bound * weighted forcing := by
    have actual : weighted velocity ≤ weighted moment + (1 + dilationConstant * changed.strain + dilationConstant * omega * epsilon) * weighted centered +
      dilationConstant * omega * epsilon * weighted raw + dilationConstant * weighted difference + dilationConstant * epsilon * ∑ patch : Fin 4, weighted (foreign ownRadius patch) := by
      simpa only [one_mul, weighted, velocity, moment, centered, raw, foreign, difference, omega, epsilon, length, macroRadius, ownRadius, first, second] using dilationData.2.2.1
    have centerTerm := mul_le_mul_of_nonneg_right (add_le_add (add_le_add_left dilationStrain 1) dilationFeedback) centeredNonnegative
    have rawTerm := mul_le_mul_of_nonneg_right dilationFeedback rawValueNonnegative
    linarith only [actual, centerTerm, rawTerm, sourceComparison dilationConstant dilationNonnegative dilationBelow]
  have dilationBound : weight * weighted dilation ≤ weighted velocity := by
    have actual : weighted dilation ≤ weighted velocity / weight := dilationData.2.2.2.2
    simpa only [mul_comm] using (le_div_iff₀ weightPositive).mp actual
  have phaseBound : weight * weighted relativePhase ≤ 2 * omega * (weighted velocity / weight) + omega * weighted shape +
      (weighted moment + weighted centered + weighted shape) + bound * (weighted centered + weighted raw) + bound * weighted forcing := by
    have actual := phaseData.2.2.2.2.2.2.2.2.2
    change weighted (fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|) ≤
      (1 + 1) * omega / weight ^ 2 * weighted velocity + 1 * omega / weight * weighted shape + (1 / weight) *
      (1 * (weighted moment + weighted centered + weighted shape) + phaseConstant * omega * epsilon * (weighted centered + weighted raw) + phaseConstant * weighted difference + phaseConstant * epsilon * ∑ patch : Fin 4, weighted (foreign ownRadius patch)) at actual
    rw [phaseIntegralEquality] at actual
    have scaled := mul_le_mul_of_nonneg_left actual weightPositive.le
    have identity : weight * ((1 + 1) * omega / weight ^ 2 * weighted velocity + 1 * omega / weight * weighted shape + (1 / weight) *
      (1 * (weighted moment + weighted centered + weighted shape) + phaseConstant * omega * epsilon * (weighted centered + weighted raw) + phaseConstant * weighted difference + phaseConstant * epsilon * ∑ patch : Fin 4, weighted (foreign ownRadius patch))) =
        2 * omega * (weighted velocity / weight) + omega * weighted shape + (weighted moment + weighted centered + weighted shape) +
        phaseConstant * omega * epsilon * (weighted centered + weighted raw) + phaseConstant * weighted difference + phaseConstant * epsilon * ∑ patch : Fin 4, weighted (foreign ownRadius patch) := by field_simp [weightPositive.ne']; ring
    rw [identity] at scaled
    have feedback := mul_le_mul_of_nonneg_right phaseFeedback (add_nonneg centeredNonnegative rawValueNonnegative)
    apply scaled.trans
    calc
      _ = (2 * omega * (weighted velocity / weight) + omega * weighted shape + (weighted moment + weighted centered + weighted shape)) +
          phaseConstant * omega * epsilon * (weighted centered + weighted raw) +
          (phaseConstant * weighted difference + phaseConstant * epsilon * ∑ patch : Fin 4, weighted (foreign ownRadius patch)) := by ring
      _ ≤ _ := add_le_add (add_le_add_left feedback _)
        (sourceComparison phaseConstant phaseNonnegative phaseBelow)
  have translationBound : weight * weighted translation ≤ weighted moment + weighted centered + weighted forcing + bound * (weighted centered + weighted raw) + bound * weighted forcing := by
    have actual : weight * weighted translation ≤ weighted moment + weighted centered + (∑ patch : Fin 4, weighted (external patch)) / (4 * location) +
      centerConstant * omega * ratio * epsilon * (weighted centered + weighted raw) + centerConstant * ratio * epsilon * ∑ patch : Fin 4, weighted (foreign ownRadius patch) := by
      simpa only [one_mul, weighted, moment, centered, raw, translation, foreign, external, ratio, omega, first, second] using centerData.2.2.2
    have feedback := mul_le_mul_of_nonneg_right centerFeedback (add_nonneg centeredNonnegative rawValueNonnegative)
    have ownCoefficient : centerConstant * ratio ≤ bound := (mul_le_of_le_one_right centerNonnegative ratioOne).trans centerBelow
    have ownSource : epsilon * (∑ patch : Fin 4, weighted (foreign ownRadius patch)) ≤ weighted forcing := by linarith only [ownBound, blockNonnegative]
    have first := mul_le_mul_of_nonneg_right ownCoefficient (mul_nonneg epsilonNonnegative (patchNonnegative ownRadius))
    have second := mul_le_mul_of_nonneg_left ownSource boundNonnegative
    nlinarith only [actual, feedback, first, second, externalBound]
  have sizeIdentity (time : ℝ) : prepared.finiteCoordinateSize graph coordinate suppliedLift index time = shape time + dilation time + relativePhase time + moment time + translation time := by
    dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize, shape, dilation, relativePhase, moment, translation, first, second, length, location]
    simp only [prepared.referenceIdentity, abs_div, abs_pow, sq_abs]
    rfl
  have expandedSizeI := (((shapeI.add dilationI).add phaseI).add momentI).add translationI
  have sizeI : IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.finiteCoordinateSize graph coordinate suppliedLift index time) volume 0 finish := by
    convert expandedSizeI using 1
    funext time
    rw [sizeIdentity]
    ring
  have sizeIntegralIdentity : weighted (prepared.finiteCoordinateSize graph coordinate suppliedLift index) = weighted shape + weighted dilation + weighted relativePhase + weighted moment + weighted translation := by
    have identity : (fun time => Real.exp (-weight * time) * prepared.finiteCoordinateSize graph coordinate suppliedLift index time) = fun time =>
      (((Real.exp (-weight * time) * shape time + Real.exp (-weight * time) * dilation time) + Real.exp (-weight * time) * relativePhase time) + Real.exp (-weight * time) * moment time) + Real.exp (-weight * time) * translation time := by
      funext time
      rw [sizeIdentity]
      ring
    dsimp only [weighted]
    rw [identity, intervalIntegral.integral_add (((shapeI.add dilationI).add phaseI).add momentI) translationI,
      intervalIntegral.integral_add ((shapeI.add dilationI).add phaseI) momentI,
      intervalIntegral.integral_add (shapeI.add dilationI) phaseI, intervalIntegral.integral_add shapeI dilationI]
  refine ⟨sizeI, shapeI, forcingI, ?_⟩
  change weighted (prepared.finiteCoordinateSize graph coordinate suppliedLift index) ≤ constant * weighted shape + (constant / weight) * weighted forcing
  rw [sizeIntegralIdentity]
  exact finite_coordinate_weighted_scalar boundOne weightOne omegaWeight centeredNonnegative rawValueNonnegative momentValueNonnegative
    velocityNonnegative shapeNonnegative forcingNonnegative neutralBound rawBound momentBound velocityBound dilationBound phaseBound translationBound

end EulerNonuniqueness.Paper
