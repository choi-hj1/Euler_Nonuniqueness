import EulerNonuniqueness.Section5.CascadeStrongNeutralSplitReconstruction
import EulerNonuniqueness.Section5.CascadeFirstMomentLocalForeignArbitraryWeightReturn
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeDilationLocalForeignArbitraryWeightReturn
import EulerNonuniqueness.Section5.CascadeCorrectedPhaseLocalForeignArbitraryWeightReturn
import EulerNonuniqueness.Section5.CascadePhaseLiftCoherence
import EulerNonuniqueness.General.TriangularNeutralAbsorption

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

open EulerNonuniqueness.Section6

private theorem strong_neutral_local_foreign_arbitrary_weight_absorb
    {constant tolerance weight omega strain epsilon ratio rawConstant momentConstant dilationConstant phaseConstant reconstructionConstant
      centered moment raw velocity dilation phase shape block macroPatch ownPatch physicalPatch : ℝ}
    (constantTwo : 2 ≤ constant) (tolerancePositive : 0 < tolerance)
    (feedbackSmall : 28 * constant ^ 3 * tolerance ≤ 1)
    (weightOne : 1 ≤ weight) (omegaNonnegative : 0 ≤ omega) (omegaBound : omega ≤ weight)
    (strainNonnegative : 0 ≤ strain) (epsilonNonnegative : 0 ≤ epsilon)
    (epsilonSmall : constant * epsilon ≤ tolerance / 4)
    (strainSmall : constant * strain ≤ tolerance * weight / 4) (ratioSmall : ratio ≤ tolerance)
    (rawNonnegative : 0 ≤ rawConstant) (rawBoundConstant : rawConstant ≤ constant)
    (momentNonnegative : 0 ≤ momentConstant) (momentBoundConstant : momentConstant ≤ constant)
    (dilationNonnegative : 0 ≤ dilationConstant) (dilationBoundConstant : dilationConstant ≤ constant)
    (phaseNonnegative : 0 ≤ phaseConstant) (phaseBoundConstant : phaseConstant ≤ constant)
    (reconstructionBoundConstant : reconstructionConstant ≤ constant)
    (centeredNonnegative : 0 ≤ centered) (momentValueNonnegative : 0 ≤ moment) (rawValueNonnegative : 0 ≤ raw)
    (velocityNonnegative : 0 ≤ velocity) (dilationValueNonnegative : 0 ≤ dilation) (phaseValueNonnegative : 0 ≤ phase)
    (shapeNonnegative : 0 ≤ shape) (blockNonnegative : 0 ≤ block) (macroNonnegative : 0 ≤ macroPatch)
    (ownNonnegative : 0 ≤ ownPatch) (physicalNonnegative : 0 ≤ physicalPatch)
    (rawEstimate : weight * raw ≤ rawConstant * omega * centered + rawConstant * physicalPatch)
    (momentEstimate : weight * moment ≤ momentConstant *
      (strain * centered + block + epsilon * (strain * raw + macroPatch)))
    (velocityEstimate : weight * velocity ≤ tolerance / 4 * moment +
      (tolerance / 4 + dilationConstant * strain + dilationConstant * omega * epsilon) * centered +
      dilationConstant * omega * epsilon * raw + dilationConstant * block + dilationConstant * epsilon * ownPatch)
    (dilationEstimate : dilation ≤ velocity)
    (phaseEstimate : weight * phase ≤ (1 + tolerance / 4) * omega * velocity +
      tolerance / 4 * omega * shape + tolerance / 4 * (moment + centered + shape) +
      phaseConstant * omega * epsilon * (centered + raw) + phaseConstant * block + phaseConstant * epsilon * ownPatch)
    (reconstruction : centered ≤ ratio * moment + reconstructionConstant * (dilation + shape + phase)) :
    centered ≤ 4 * constant * shape + 28 * constant ^ 4 *
      ((block + epsilon * macroPatch + epsilon * ownPatch + epsilon * physicalPatch) / weight) := by
  have constantOne : 1 ≤ constant := by linarith
  have constantNonnegative : 0 ≤ constant := by linarith
  have weightPositive : 0 < weight := by linarith
  have toleranceOne : tolerance ≤ 1 := by
    have cubeOne := one_le_pow₀ constantOne (n := 3)
    nlinarith [mul_le_mul_of_nonneg_right cubeOne tolerancePositive.le]
  let forcing := (block + epsilon * macroPatch + epsilon * ownPatch + epsilon * physicalPatch) / weight
  have forcingNonnegative : 0 ≤ forcing := by dsimp only [forcing]; positivity
  have forcingIdentity : weight * forcing = block + epsilon * macroPatch + epsilon * ownPatch + epsilon * physicalPatch := by
    dsimp only [forcing]
    field_simp [weightPositive.ne']
  have sourceMacro : block + epsilon * macroPatch ≤ weight * forcing := by
    rw [forcingIdentity]
    nlinarith [mul_nonneg epsilonNonnegative ownNonnegative, mul_nonneg epsilonNonnegative physicalNonnegative]
  have sourceOwn : block + epsilon * ownPatch ≤ weight * forcing := by
    rw [forcingIdentity]
    nlinarith [mul_nonneg epsilonNonnegative macroNonnegative, mul_nonneg epsilonNonnegative physicalNonnegative]
  have sourcePhysical : epsilon * physicalPatch ≤ weight * forcing := by
    rw [forcingIdentity]
    nlinarith [mul_nonneg epsilonNonnegative macroNonnegative, mul_nonneg epsilonNonnegative ownNonnegative]
  have feedback (coefficient : ℝ) (nonnegative : 0 ≤ coefficient) (bounded : coefficient ≤ constant) :
      coefficient * omega * epsilon ≤ tolerance * weight / 4 := by
    have first := mul_le_mul_of_nonneg_right bounded epsilonNonnegative
    have second := mul_le_mul_of_nonneg_right (first.trans epsilonSmall) omegaNonnegative
    have third := mul_le_mul_of_nonneg_left omegaBound (show 0 ≤ tolerance / 4 by positivity)
    nlinarith only [second, third]
  have strainFeedback (coefficient : ℝ) (bounded : coefficient ≤ constant) :
      coefficient * strain ≤ tolerance * weight / 4 :=
    (mul_le_mul_of_nonneg_right bounded strainNonnegative).trans strainSmall
  have coefficientOmega (coefficient : ℝ) (nonnegative : 0 ≤ coefficient) (bounded : coefficient ≤ constant) :
      coefficient * omega ≤ constant * weight :=
    (mul_le_mul_of_nonneg_right bounded omegaNonnegative).trans (mul_le_mul_of_nonneg_left omegaBound constantNonnegative)
  have pointTolerance : tolerance / 4 ≤ tolerance * weight / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left weightOne tolerancePositive.le]
  have rawAbsorbed : epsilon * raw ≤ tolerance * centered + constant * forcing := by
    apply (mul_le_mul_right weightPositive).mp
    have scaled := mul_le_mul_of_nonneg_left rawEstimate epsilonNonnegative
    have localTerm := mul_le_mul_of_nonneg_right (feedback rawConstant rawNonnegative rawBoundConstant) centeredNonnegative
    have source := (mul_le_mul_of_nonneg_left sourcePhysical rawNonnegative).trans
      (mul_le_mul_of_nonneg_right rawBoundConstant (mul_nonneg weightPositive.le forcingNonnegative))
    nlinarith only [scaled, localTerm, source, mul_nonneg (mul_nonneg tolerancePositive.le weightPositive.le) centeredNonnegative]
  have momentAbsorbed : moment ≤ tolerance * (centered + epsilon * raw) + constant * forcing := by
    apply (mul_le_mul_right weightPositive).mp
    have localTerm := mul_le_mul_of_nonneg_right (strainFeedback momentConstant momentBoundConstant)
      (show 0 ≤ centered + epsilon * raw by positivity)
    have source := (mul_le_mul_of_nonneg_left sourceMacro momentNonnegative).trans
      (mul_le_mul_of_nonneg_right momentBoundConstant (mul_nonneg weightPositive.le forcingNonnegative))
    nlinarith only [momentEstimate, localTerm, source,
      mul_nonneg (mul_nonneg tolerancePositive.le weightPositive.le) (show 0 ≤ centered + epsilon * raw by positivity)]
  have velocityAbsorbed : velocity ≤ tolerance * moment + tolerance * centered +
      constant * (epsilon * raw) + constant * forcing := by
    apply (mul_le_mul_right weightPositive).mp
    have momentTerm := mul_le_mul_of_nonneg_right pointTolerance momentValueNonnegative
    have centerTerm := mul_le_mul_of_nonneg_right
      (add_le_add (add_le_add pointTolerance (strainFeedback dilationConstant dilationBoundConstant))
        (feedback dilationConstant dilationNonnegative dilationBoundConstant)) centeredNonnegative
    have rawTerm := mul_le_mul_of_nonneg_right (coefficientOmega dilationConstant dilationNonnegative dilationBoundConstant)
      (show 0 ≤ epsilon * raw by positivity)
    have source := (mul_le_mul_of_nonneg_left sourceOwn dilationNonnegative).trans
      (mul_le_mul_of_nonneg_right dilationBoundConstant (mul_nonneg weightPositive.le forcingNonnegative))
    nlinarith only [velocityEstimate, momentTerm, centerTerm, rawTerm, source,
      mul_nonneg (mul_nonneg tolerancePositive.le weightPositive.le) momentValueNonnegative,
      mul_nonneg (mul_nonneg tolerancePositive.le weightPositive.le) centeredNonnegative]
  have phaseAbsorbed : phase ≤ constant * velocity + tolerance * moment + tolerance * centered +
      tolerance * shape + constant * (epsilon * raw) + constant * forcing := by
    apply (mul_le_mul_right weightPositive).mp
    have omegaTerm := mul_le_mul_of_nonneg_left omegaBound (show 0 ≤ 1 + tolerance / 4 by positivity)
    have coefficient : 1 + tolerance / 4 ≤ constant := by linarith
    have velocityTerm := mul_le_mul_of_nonneg_right (omegaTerm.trans
      (mul_le_mul_of_nonneg_right coefficient weightPositive.le)) velocityNonnegative
    have momentTerm := mul_le_mul_of_nonneg_right pointTolerance momentValueNonnegative
    have centerTerm := mul_le_mul_of_nonneg_right (add_le_add pointTolerance
      (feedback phaseConstant phaseNonnegative phaseBoundConstant)) centeredNonnegative
    have shapeTerm := mul_le_mul_of_nonneg_right (add_le_add
      (mul_le_mul_of_nonneg_left omegaBound (show 0 ≤ tolerance / 4 by positivity)) pointTolerance) shapeNonnegative
    have rawTerm := mul_le_mul_of_nonneg_right (coefficientOmega phaseConstant phaseNonnegative phaseBoundConstant)
      (show 0 ≤ epsilon * raw by positivity)
    have source := (mul_le_mul_of_nonneg_left sourceOwn phaseNonnegative).trans
      (mul_le_mul_of_nonneg_right phaseBoundConstant (mul_nonneg weightPositive.le forcingNonnegative))
    nlinarith only [phaseEstimate, velocityTerm, momentTerm, centerTerm, shapeTerm, rawTerm, source,
      mul_nonneg (mul_nonneg tolerancePositive.le weightPositive.le) momentValueNonnegative,
      mul_nonneg (mul_nonneg tolerancePositive.le weightPositive.le) centeredNonnegative,
      mul_nonneg (mul_nonneg tolerancePositive.le weightPositive.le) shapeNonnegative]
  have reconstructionAbsorbed : centered ≤ tolerance * moment + constant * (dilation + shape + phase) :=
    reconstruction.trans (add_le_add (mul_le_mul_of_nonneg_right ratioSmall momentValueNonnegative)
      (mul_le_mul_of_nonneg_right reconstructionBoundConstant (by positivity)))
  exact EulerNonuniqueness.General.triangular_neutral_response_le_of_small_feedback constantOne tolerancePositive.le feedbackSmall
    centeredNonnegative shapeNonnegative forcingNonnegative rawAbsorbed momentAbsorbed velocityAbsorbed
    dilationEstimate phaseAbsorbed reconstructionAbsorbed

theorem exists_uniform_actual_strong_neutral_local_foreign_arbitrary_weight_return
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (0 : ℝ), ∃ rootMin ≥ (8 : ℝ),
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
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
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
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let macroRadius := factor / 39321600 * changed.location (index.val + 1)
    let ownRadius := factor / 39321600 * changed.length (index.val + 1)
    let historyIntegral := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
    let shape := fun time =>
      |(referenceStraightenedShape first.patchMotion graph coordinate index time).1 -
        (referenceStraightenedShape second.patchMotion graph coordinate index time).1| +
      |(referenceStraightenedShape first.patchMotion graph coordinate index time).2 -
        (referenceStraightenedShape second.patchMotion graph coordinate index time).2|
    let difference := fun time => ∑' power : ℕ,
      ‖quadrupoleExteriorCoefficient changed first.patchMotion index time macroRadius power -
        quadrupoleExteriorCoefficient changed second.patchMotion index time macroRadius power‖
    let foreign := fun (receiverRadius : ℝ) (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) receiverRadius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) receiverRadius (power + 1) time‖
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) volume 0 finish ∧
      historyIntegral (fun time => prepared.rawSourceCenteredState time index) ≤ constant * historyIntegral shape +
        (constant / weight) * (historyIntegral difference +
          epsilon * ∑ patch : Fin 4, historyIntegral (foreign macroRadius patch) +
          epsilon * ∑ patch : Fin 4, historyIntegral (foreign ownRadius patch) +
          epsilon * ∑ patch : Fin 4, historyIntegral (foreign (changed.radius (index.val + 1)) patch)) := by
  obtain ⟨reconstructionRadius, reconstructionPositive, reconstructionQuarter, reconstructionConstant,
    reconstructionOne, reconstruct⟩ := exists_uniform_cascade_strong_neutral_split_reconstruction
      graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨momentCap, momentPositive, moments⟩ := exists_uniform_actual_firstMoment_local_foreign_arbitrary_weight_return
  obtain ⟨rawSourceCap, rawSourcePositive, raws⟩ := exists_uniform_actual_raw_source_weighted_local_foreign_return
  obtain ⟨dilationCap, dilationPositive, dilations⟩ := exists_uniform_actual_prehit_dilation_local_foreign_arbitrary_weight_return
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, phaseCap, phasePositive, phases⟩ :=
    exists_uniform_actual_cascade_corrected_phase_local_foreign_arbitrary_weight_return graphAnalytic graphZero graphDerivative
      coordinateSmooth coordinateZero coordinateDerivative
  let rawCap := min momentCap (min rawSourceCap (min dilationCap phaseCap))
  have capPositive : 0 < rawCap := lt_min momentPositive (lt_min rawSourcePositive (lt_min dilationPositive phasePositive))
  have momentCapBound : rawCap ≤ momentCap := min_le_left _ _
  have rawCapBound : rawCap ≤ rawSourceCap := (min_le_right _ _).trans (min_le_left _ _)
  have dilationCapBound : rawCap ≤ dilationCap :=
    ((min_le_right momentCap _).trans (min_le_right rawSourceCap _)).trans (min_le_left _ _)
  have phaseCapBound : rawCap ≤ phaseCap :=
    ((min_le_right momentCap _).trans (min_le_right rawSourceCap _)).trans (min_le_right _ _)
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨momentConstant, momentNonnegative, momentFactory⟩ := moments factorPositive factorEighth
  obtain ⟨rawConstant, rawNonnegative, rootMin, rootEight, rawFactory⟩ := raws factor factorPositive factorOne
  obtain ⟨dilationConstant, dilationNonnegative, dilationFactory⟩ := dilations factorPositive factorSmall
  obtain ⟨phaseConstant, phaseNonnegative, phaseFactory⟩ := phases factorPositive factorEighth
  let boundConstant := 2 + rawConstant + 2 * momentConstant + dilationConstant + phaseConstant + reconstructionConstant
  have boundTwo : 2 ≤ boundConstant := by dsimp only [boundConstant]; linarith
  have boundPositive : 0 < boundConstant := by linarith
  have rawConstantBound : rawConstant ≤ boundConstant := by dsimp only [boundConstant]; linarith
  have momentConstantBound : 2 * momentConstant ≤ boundConstant := by dsimp only [boundConstant]; linarith
  have dilationConstantBound : dilationConstant ≤ boundConstant := by dsimp only [boundConstant]; linarith
  have phaseConstantBound : phaseConstant ≤ boundConstant := by dsimp only [boundConstant]; linarith
  have reconstructionConstantBound : reconstructionConstant ≤ boundConstant := by dsimp only [boundConstant]; linarith
  let tolerance := 1 / (28 * boundConstant ^ 3)
  have tolerancePositive : 0 < tolerance := by dsimp only [tolerance]; positivity
  have feedbackSmall : 28 * boundConstant ^ 3 * tolerance ≤ 1 := by
    dsimp only [tolerance]
    field_simp [boundPositive.ne']
  obtain ⟨phaseRadius, phaseRadiusPositive, phaseRadiusQuarter, phaseParameters⟩ :=
    phaseFactory (tolerance / 4) (by positivity)
  let radius := min reconstructionRadius phaseRadius
  refine ⟨radius, lt_min reconstructionPositive phaseRadiusPositive, (min_le_left _ _).trans reconstructionQuarter,
    28 * boundConstant ^ 4, by positivity, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive orbit sectionTime threshold referenceConstant
    boundaryConstant thresholdSmall referenceNonnegative boundaryOne
  have rootOne : 1 ≤ scaleRoot := by linarith [rootEight.trans rootLarge]
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdEighthBound : threshold ≤ 1 / 8 := thresholdSmall.trans thresholdEighth
  let small := tolerance / (4 * boundConstant)
  have smallPositive : 0 < small := by dsimp only [small]; positivity
  filter_upwards [momentFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdEighthBound
      referenceNonnegative rootOne boundaryOne,
    rawFactory scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
      thresholdEighthBound referenceNonnegative boundaryOne orbit sectionTime,
    dilationFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdEighthBound referenceNonnegative (show 0 < tolerance / 4 by positivity),
    phaseParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    reconstruct scales amplitudePositive ratioBound alphaPositive (by linarith only [rootOne]) (by linarith only [boundaryOne])
      factorEighth thresholdEighthBound referenceNonnegative,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound]) (Real.sqrt_pos.mpr smallPositive),
    scales.eventually_length_lt_location ratioBound alphaPositive (show 0 < 4 * tolerance by positivity),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds smallPositive),
    eventually_ge_atTop (1 : ℝ)]
    with frequency momentEstimate rawEstimate dilationEstimate phaseEstimate coherence reconstruction radii lengths strainSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall chartSmall
    suppliedLift suppliedContinuous suppliedInitial suppliedPolar weight omegaWeight
  dsimp only
  by_cases finishZero : finish = 0
  · subst finish
    refine ⟨IntervalIntegrable.refl, ?_⟩
    simp only [intervalIntegral.integral_same, mul_zero, Finset.sum_const_zero, add_zero, le_refl]
  have finishPositive : 0 < finish := lt_of_le_of_ne finishNonnegative (Ne.symm finishZero)
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let macroRadius := factor / 39321600 * changed.location (index.val + 1)
  let ownRadius := factor / 39321600 * changed.length (index.val + 1)
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  let shape := fun time =>
    |(referenceStraightenedShape first.patchMotion graph coordinate index time).1 -
      (referenceStraightenedShape second.patchMotion graph coordinate index time).1| +
    |(referenceStraightenedShape first.patchMotion graph coordinate index time).2 -
      (referenceStraightenedShape second.patchMotion graph coordinate index time).2|
  let difference := fun time => ∑' power : ℕ,
    ‖quadrupoleExteriorCoefficient changed first.patchMotion index time macroRadius power -
      quadrupoleExteriorCoefficient changed second.patchMotion index time macroRadius power‖
  let foreign := fun (receiverRadius : ℝ) (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) receiverRadius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) receiverRadius (power + 1) time‖
  let centeredIntegral := weighted (fun time => prepared.rawSourceCenteredState time index)
  let rawIntegral := weighted (fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch)
  let momentIntegral := weighted (fun time => ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖)
  let velocityIntegral := weighted (fun time => |relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index time|)
  let dilationIntegral := weighted (fun time => |(diagonalDifference first.patchMotion time index - diagonalDifference second.patchMotion time index) /
    changed.length (index.val + 1) ^ 2|)
  let patchIntegral := fun receiverRadius => ∑ patch : Fin 4, weighted (foreign receiverRadius patch)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have weightOne : 1 ≤ weight := omegaOne.trans omegaWeight
  have weightPositive : 0 < weight := by linarith
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have epsilonSmall : boundConstant * epsilon ≤ tolerance / 4 := by
    have actual := pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le
      (radii (index.val + 1)).le 2
    rw [mul_pow, Real.sq_sqrt smallPositive.le] at actual
    have divided : epsilon ≤ small := (div_le_iff₀ (sq_pos_of_pos (changed.length_pos _))).mpr actual
    apply (mul_le_mul_of_nonneg_left divided boundPositive.le).trans_eq
    dsimp only [small]
    field_simp
    ring
  have strainFeedback : boundConstant * changed.strain ≤ tolerance * weight / 4 := by
    have actual := mul_le_mul_of_nonneg_left strainSmall.le boundPositive.le
    have identity : boundConstant * small = tolerance / 4 := by dsimp only [small]; field_simp; ring
    rw [identity] at actual
    exact actual.trans (by nlinarith [mul_le_mul_of_nonneg_left weightOne tolerancePositive.le])
  have ratioSmall : changed.length (index.val + 1) / (4 * changed.location (index.val + 1)) ≤ tolerance := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) (changed.location_pos _))).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using (lengths (index.val + 1)).le
  have integralNonnegative (function : ℝ → ℝ) (nonnegative : ∀ time, 0 ≤ function time) : 0 ≤ weighted function :=
    intervalIntegral.integral_nonneg_of_forall finishNonnegative (fun time => mul_nonneg (Real.exp_pos _).le (nonnegative time))
  have centeredNonnegative : 0 ≤ centeredIntegral := integralNonnegative _ (fun time => by
    exact div_nonneg (norm_nonneg _) (changed.length_pos _).le)
  have rawValueNonnegative : 0 ≤ rawIntegral := integralNonnegative _ (fun time => Finset.sum_nonneg (fun patch _ => by
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity))
  have momentValueNonnegative : 0 ≤ momentIntegral := integralNonnegative _ (fun _ => norm_nonneg _)
  have velocityValueNonnegative : 0 ≤ velocityIntegral := integralNonnegative _ (fun _ => abs_nonneg _)
  have dilationValueNonnegative : 0 ≤ dilationIntegral := integralNonnegative _ (fun _ => abs_nonneg _)
  have shapeNonnegative : 0 ≤ weighted shape := integralNonnegative _ (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  have blockNonnegative : 0 ≤ weighted difference := integralNonnegative _ (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
  have patchNonnegative (receiverRadius : ℝ) : 0 ≤ patchIntegral receiverRadius := Finset.sum_nonneg (fun patch _ =>
    integralNonnegative _ (fun _ => tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _))))
  have momentActual := momentEstimate count phase dipoleAngle (prepared.enlargeCap momentCapBound) path index nonterminal
    finish finishNonnegative finishBound radialSmall weight omegaWeight
  rcases momentActual with ⟨blockIntegrable, macroIntegrable, centeredIntegrable, rawIntegrable, momentIntegrable, momentBound⟩
  have rawActual := rawEstimate count phase dipoleAngle (prepared.enlargeCap rawCapBound) path index finish
    finishNonnegative finishBound weight omegaWeight
  rcases rawActual with ⟨physicalIntegrable, _, rawBound⟩
  have dilationActual := dilationEstimate count phase dipoleAngle (prepared.enlargeCap dilationCapBound) path index nonterminal
    finish finishNonnegative finishBound radialSmall weight omegaWeight
  rcases dilationActual with ⟨dilationIntegrable, velocityIntegrable, velocityBound, dilationBound, dilationDirect⟩
  obtain ⟨lift, liftContinuous, polar, phaseAllWeights⟩ := phaseEstimate count phase dipoleAngle (prepared.enlargeCap phaseCapBound) path
    index nonterminal finish finishPositive finishBound radialSmall
    (fun time inside => (chartSmall time inside).trans (min_le_right _ _))
  have phaseActual := phaseAllWeights weight omegaWeight
  rcases phaseActual with ⟨phaseIntegrable, _, shapeIntegrable, forcingIntegrable, _, _, _, _, ownIntegrable, phaseBound⟩
  let phaseIntegral := weighted (fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) suppliedLift
    (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|)
  have liftEquality := coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (chartSmall time inside).trans ((min_le_left _ _).trans reconstructionQuarter))
    lift suppliedLift (fun side => (liftContinuous side).1.continuousOn) suppliedContinuous
    (fun side => (liftContinuous side).2.trans (suppliedInitial side).symm) polar suppliedPolar
  have phaseIntegralEquality :
      weighted (fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
        (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|) = phaseIntegral := by
    dsimp only [weighted, phaseIntegral]
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le finishNonnegative] at inside
    exact congrArg (fun value : ℝ => Real.exp (-weight * time) * |value|)
      (liftEquality.2.1 (phaseCorrection 1 graph) inside)
  have phaseValueNonnegative : 0 ≤ phaseIntegral := integralNonnegative _ (fun _ => abs_nonneg _)
  have foreignSwap (patch : Fin 4) (time : ℝ) :
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid second.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time -
          first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid first.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time‖) =
        foreign (changed.radius (index.val + 1)) patch time := by
    apply tsum_congr
    intro power
    dsimp only [foreign]
    rw [norm_sub_rev]
  have rawScalar : weight * rawIntegral ≤ rawConstant * omega * centeredIntegral +
      rawConstant * patchIntegral (changed.radius (index.val + 1)) := by
    dsimp only at rawBound
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState,
        CascadeSourcePreparedPair.rawSourceShapeBudget] at rawBound
    change weight * rawIntegral ≤ rawConstant * omega * centeredIntegral + rawConstant *
      ∑ patch : Fin 4, weighted (fun time => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid second.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time -
          first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid first.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time‖) at rawBound
    simp_rw [foreignSwap] at rawBound
    exact rawBound
  have momentScalar : weight * momentIntegral ≤ (2 * momentConstant) *
      (changed.strain * centeredIntegral + weighted difference + epsilon * (changed.strain * rawIntegral + patchIntegral macroRadius)) := by
    dsimp only [CascadeSourcePreparedPair.enlargeCap] at momentBound
    rw [prepared.referenceIdentity] at momentBound
    with_reducible_and_instances
      dsimp only [weighted, momentIntegral, centeredIntegral, rawIntegral, patchIntegral, foreign, difference, changed, first, second,
        omega, epsilon, macroRadius, CascadeSourcePreparedPair.enlargeCap,
        CascadeSourcePreparedPair.rawSourceCenteredState, CascadeSourcePreparedPair.rawSourceShapeBudget] at momentBound ⊢
      exact momentBound
  have velocityScalar : weight * (velocityIntegral / weight) ≤ tolerance / 4 * momentIntegral +
      (tolerance / 4 + dilationConstant * changed.strain + dilationConstant * omega * epsilon) * centeredIntegral +
      dilationConstant * omega * epsilon * rawIntegral + dilationConstant * weighted difference + dilationConstant * epsilon * patchIntegral ownRadius := by
    rw [mul_div_cancel₀ _ weightPositive.ne']
    with_reducible_and_instances
      dsimp only [weighted, velocityIntegral, momentIntegral, centeredIntegral, rawIntegral, patchIntegral, foreign, difference,
        changed, first, second, omega, epsilon, macroRadius, ownRadius, CascadeSourcePreparedPair.enlargeCap,
        CascadeSourcePreparedPair.rawSourceCenteredState, CascadeSourcePreparedPair.rawSourceShapeBudget] at velocityBound ⊢
      exact velocityBound
  have dilationScalar : dilationIntegral ≤ velocityIntegral / weight := by
    with_reducible_and_instances
      dsimp only [weighted, dilationIntegral, velocityIntegral, first, second, changed, omega,
        CascadeSourcePreparedPair.enlargeCap] at dilationDirect ⊢
      exact dilationDirect
  have phaseScalar : weight * phaseIntegral ≤ (1 + tolerance / 4) * omega * (velocityIntegral / weight) +
      tolerance / 4 * omega * weighted shape + tolerance / 4 * (momentIntegral + centeredIntegral + weighted shape) +
      phaseConstant * omega * epsilon * (centeredIntegral + rawIntegral) + phaseConstant * weighted difference +
      phaseConstant * epsilon * patchIntegral ownRadius := by
    have normalized : weighted (fun time => |relativeCorrectedPaperPhase (phaseCorrection 1 graph) lift
        (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time|) ≤ (1 + tolerance / 4) * omega / weight ^ 2 * velocityIntegral +
        tolerance / 4 * omega / weight * weighted shape + (1 / weight) *
        (tolerance / 4 * (momentIntegral + centeredIntegral + weighted shape) +
          phaseConstant * omega * epsilon * (centeredIntegral + rawIntegral) + phaseConstant * weighted difference +
          phaseConstant * epsilon * patchIntegral ownRadius) := by
      with_reducible_and_instances
        dsimp only [weighted, velocityIntegral, momentIntegral, centeredIntegral, rawIntegral, patchIntegral,
          foreign, difference, shape, changed, first, second, omega, epsilon, macroRadius, ownRadius,
          CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState,
          CascadeSourcePreparedPair.rawSourceShapeBudget] at phaseBound ⊢
        exact phaseBound
    rw [phaseIntegralEquality] at normalized
    convert mul_le_mul_of_nonneg_left normalized weightPositive.le using 1; field_simp [weightPositive.ne']; ring
  have reconstructed : centeredIntegral ≤
      (changed.length (index.val + 1) / (4 * changed.location (index.val + 1))) * momentIntegral +
        reconstructionConstant * (dilationIntegral + weighted shape + phaseIntegral) := by
    have actual := reconstruction prepared.toCascadeMaterialPreparedPair path index nonterminal finish finishNonnegative finishBound
      (fun time inside => (chartSmall time inside).trans (min_le_left _ _)) suppliedLift
      suppliedContinuous suppliedPolar weight
    rw [prepared.referenceIdentity] at actual
    with_reducible_and_instances
      dsimp only [weighted, centeredIntegral, momentIntegral, dilationIntegral, phaseIntegral, shape, first, second, changed,
        omega, CascadeSourcePreparedPair.rawSourceCenteredState] at actual ⊢
      simpa only [abs_div, abs_pow, sq_abs, norm_sub_rev, add_assoc] using actual
  have absorbed := strong_neutral_local_foreign_arbitrary_weight_absorb boundTwo tolerancePositive feedbackSmall weightOne omegaPositive.le omegaWeight
    strainNonnegative epsilonNonnegative epsilonSmall strainFeedback ratioSmall rawNonnegative rawConstantBound
    (mul_nonneg (by norm_num) momentNonnegative) momentConstantBound dilationNonnegative dilationConstantBound
    phaseNonnegative phaseConstantBound reconstructionConstantBound centeredNonnegative momentValueNonnegative rawValueNonnegative
    (div_nonneg velocityValueNonnegative weightPositive.le) dilationValueNonnegative phaseValueNonnegative shapeNonnegative blockNonnegative
    (patchNonnegative macroRadius) (patchNonnegative ownRadius) (patchNonnegative (changed.radius (index.val + 1)))
    rawScalar momentScalar velocityScalar dilationScalar phaseScalar reconstructed
  have finalCoefficient : 4 * boundConstant ≤ 28 * boundConstant ^ 4 := by
    have cube := one_le_pow₀ (show 1 ≤ boundConstant by linarith) (n := 3)
    have actual := mul_le_mul_of_nonneg_left cube boundPositive.le
    nlinarith only [actual, boundPositive.le]
  refine ⟨?_, absorbed.trans ?_⟩
  · with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState] at centeredIntegrable ⊢
      exact centeredIntegrable
  · have actual := mul_le_mul_of_nonneg_right finalCoefficient shapeNonnegative
    change 4 * boundConstant * weighted shape + 28 * boundConstant ^ 4 *
      ((weighted difference + epsilon * patchIntegral macroRadius + epsilon * patchIntegral ownRadius +
        epsilon * patchIntegral (changed.radius (index.val + 1))) / weight) ≤
      28 * boundConstant ^ 4 * weighted shape + (28 * boundConstant ^ 4 / weight) *
        (weighted difference + epsilon * patchIntegral macroRadius + epsilon * patchIntegral ownRadius +
          epsilon * patchIntegral (changed.radius (index.val + 1)))
    calc
      _ ≤ 28 * boundConstant ^ 4 * weighted shape + 28 * boundConstant ^ 4 *
          ((weighted difference + epsilon * patchIntegral macroRadius + epsilon * patchIntegral ownRadius +
            epsilon * patchIntegral (changed.radius (index.val + 1))) / weight) := add_le_add_right actual _
      _ = _ := by ring

end EulerNonuniqueness.Paper

