import EulerNonuniqueness.Section5.CascadeMixedFollowerClosedPrefixBudget
import EulerNonuniqueness.Section5.CascadeFollowerEliminatedWeightedForcing

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def CascadeSourcePreparedPair.mixedFollowerSourcePrefixBudget
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ} (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold
      referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (drive : Fin count) (incomingConstant outgoingConstant extent coefficient : ℝ)
    (entry initialDistance magnitude : Fin count → ℝ) (weight finish : ℝ) : ℝ :=
  let finer := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  incomingConstant * extent ^ 2 * (∑ source ∈ finer,
    scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 *
      (1 + (scales.location (source.val + 1))⁻¹) * magnitude source /
      (coefficient * scales.omega (source.val + 1)) * Real.exp (-weight * entry source)) +
  outgoingConstant * (∑ source ∈ finer.filter (fun source => entry source < finish),
    scales.circulation (source.val + 1) * (scales.circulation (source.val + 1) / weight ^ 2 +
      ((1 + initialDistance source) * scales.length (source.val + 1) ^ 2 +
        ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion (entry source) source‖) / weight) *
      Real.exp (-weight * entry source))

private theorem mixed_closed_feedback_scalar
    {allValue shape finer remaining macroValue known first returnCoefficient driverCoefficient macroShape macroFeedback tolerance : ℝ}
    (allNonnegative : 0 ≤ allValue) (shapeNonnegative : 0 ≤ shape)
    (returnNonnegative : 0 ≤ returnCoefficient) (driverNonnegative : 0 ≤ driverCoefficient)
    (eliminated : allValue ≤ first * shape + 2 * finer + returnCoefficient * remaining)
    (closed : remaining ≤ 2 * known + driverCoefficient * macroValue)
    (macroBound : macroValue ≤ macroShape * shape + macroFeedback * allValue)
    (feedback : returnCoefficient * driverCoefficient * macroFeedback ≤ 1 / 2)
    (shapeBound : 2 * (first + returnCoefficient * driverCoefficient * macroShape) ≤ tolerance) :
    allValue ≤ tolerance * shape + 4 * finer + 4 * returnCoefficient * known := by
  have scaledClosed := mul_le_mul_of_nonneg_left closed returnNonnegative
  have scaledMacro := mul_le_mul_of_nonneg_left macroBound (mul_nonneg returnNonnegative driverNonnegative)
  have scaledFeedback := mul_le_mul_of_nonneg_right feedback allNonnegative
  have scaledShape := mul_le_mul_of_nonneg_right shapeBound shapeNonnegative
  nlinarith only [eliminated, scaledClosed, scaledMacro, scaledFeedback, scaledShape]

theorem exists_uniform_actual_mixed_follower_closed_weighted_forcing
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
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
    let finerForcing := prepared.selectedForeignForcing
      (Finset.univ.filter (fun source : Fin count => drive.val < source.val ∧ source ≠ drive)) drive
    let remaining := prepared.followerStrictlyFinerForcing drive
    let shape := fun time =>
      |(referenceStraightenedShape motion graph coordinate drive time).1 -
        (referenceStraightenedShape prepared.referenceWitness.trajectory.movingFamily.patchMotion graph coordinate drive time).1| +
      |(referenceStraightenedShape motion graph coordinate drive time).2 -
        (referenceStraightenedShape prepared.referenceWitness.trajectory.movingFamily.patchMotion graph coordinate drive time).2|
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
    ContinuousOn allForcing (Icc 0 finish) ∧ ContinuousOn finerForcing (Icc 0 finish) ∧
    ContinuousOn remaining (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.macroSourceState time drive) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * shape time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * allForcing time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * finerForcing time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * remaining time) volume 0 finish ∧
    (∀ time ∈ Icc 0 finish, prepared.finiteCoordinateForeignForcing drive time +
      prepared.physicalForeignSourceForcing drive time ≤ allForcing time) ∧
    weighted allForcing ≤ tolerance * weighted shape + 4 * weighted finerForcing +
      (16 * followerConstant * rho / (changed.omega (drive.val + 1) * changed.location (drive.val + 1) ^ 4)) *
        prepared.mixedFollowerSourcePrefixBudget drive incomingConstant outgoingConstant extent coefficient
          entry initialDistance magnitude weight finish := by
  obtain ⟨closedThreshold, closedPositive, closedEighth, closedCap, closedCapPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, closedFactory⟩ :=
    exists_uniform_actual_mixed_follower_closed_prefix_budget
  obtain ⟨eliminatedThreshold, eliminatedPositive, _, eliminatedCap, eliminatedCapPositive, eliminatedFactory⟩ :=
    exists_uniform_actual_follower_eliminated_weighted_forcing graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨macroThreshold, macroPositive, _, macroCap, macroCapPositive, macroFactory⟩ :=
    exists_uniform_actual_macro_state_shape_arbitrary_weight_response graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  let thresholdMax := min closedThreshold (min eliminatedThreshold macroThreshold)
  let rawCap := min closedCap (min eliminatedCap macroCap)
  have closedCapBound : rawCap ≤ closedCap := min_le_left _ _
  have eliminatedCapBound : rawCap ≤ eliminatedCap := (min_le_right _ _).trans (min_le_left _ _)
  have macroCapBound : rawCap ≤ macroCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨thresholdMax, lt_min closedPositive (lt_min eliminatedPositive macroPositive),
    (min_le_left _ _).trans closedEighth, rawCap, lt_min closedCapPositive (lt_min eliminatedCapPositive macroCapPositive),
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨closedRadius, closedRadiusPositive, closedQuarter, responseConstant, responseOne, closedRoot, closedEight, closedResponses⟩ :=
    closedFactory factorPositive factorSmall
  obtain ⟨eliminatedRadius, eliminatedRadiusPositive, _, eliminationMacro, eliminationMacroOne,
    followerConstant, followerOne, eliminatedRoot, _, eliminations⟩ := eliminatedFactory factor factorPositive factorSmall
  obtain ⟨macroRadius, macroRadiusPositive, _, macroConstant, macroOne, macroRoot, _, macros⟩ := macroFactory factor factorPositive factorSmall
  let radius := min closedRadius (min eliminatedRadius macroRadius)
  let ratioMin := max 2 (max (4 * followerConstant) (4 * responseConstant))
  let rootMin := max closedRoot (max eliminatedRoot macroRoot)
  refine ⟨radius, lt_min closedRadiusPositive (lt_min eliminatedRadiusPositive macroRadiusPositive),
    (min_le_left _ _).trans closedQuarter, followerConstant, followerOne, ratioMin,
    max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _)), rootMin,
    closedEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive extent extentOne referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant tolerance boundaryOne tolerancePositive
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have followerRatio : max 2 (4 * followerConstant) ≤ scales.ratio :=
    (max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))).trans ratioLarge
  have responseRatio : max 2 (4 * responseConstant) ≤ scales.ratio :=
    (max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))).trans ratioLarge
  let eta := tolerance / (8 * eliminationMacro)
  have etaPositive : 0 < eta := div_pos tolerancePositive (by positivity)
  let product := 32 * followerConstant * responseConstant * macroConstant
  have productPositive : 0 < product := by dsimp only [product]; positivity
  have rhoDecay := ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
    ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)
  have productDecay := rhoDecay.const_mul product
  simp only [mul_zero, zero_add] at productDecay
  have smallPositive : 0 < min (1 : ℝ) (tolerance / 2) := lt_min zero_lt_one (half_pos tolerancePositive)
  filter_upwards [closedResponses scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity responseRatio alphaPositive
      extent extentOne referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans (min_le_left _ _))
      orbit sectionTime boundaryConstant boundaryOne,
    eliminations scales scaleRoot ((le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)) amplitudeIdentity followerRatio
      alphaPositive threshold referenceConstant boundaryConstant (thresholdBound.trans ((min_le_right _ _).trans (min_le_left _ _)))
      referenceNonnegative boundaryOne orbit sectionTime eta etaPositive,
    macros scales scaleRoot ((le_max_right _ _).trans ((le_max_right _ _).trans rootLarge)) amplitudeIdentity ratioBound alphaPositive
      orbit sectionTime (thresholdBound.trans ((min_le_right _ _).trans (min_le_right _ _))) referenceNonnegative boundaryOne,
    productDecay.eventually (eventually_lt_nhds smallPositive), eventually_ge_atTop (1 : ℝ)]
    with frequency closedResponse elimination macroResponse productSmall frequencyOne
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
  let remaining := prepared.followerStrictlyFinerForcing drive
  let shape := fun time =>
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate drive time).1 -
      (referenceStraightenedShape prepared.referenceWitness.trajectory.movingFamily.patchMotion graph coordinate drive time).1| +
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate drive time).2 -
      (referenceStraightenedShape prepared.referenceWitness.trajectory.movingFamily.patchMotion graph coordinate drive time).2|
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  let known := prepared.mixedFollowerSourcePrefixBudget drive incomingConstant outgoingConstant extent coefficient
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
  have remainingInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).followerStrictlyFinerForcing = prepared.followerStrictlyFinerForcing := rfl
  have weightedInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).weightedMacroSourceState = prepared.weightedMacroSourceState := by
    funext time source
    simp only [CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  have eliminatedData := elimination count phase dipoleAngle (prepared.enlargeCap eliminatedCapBound) path drive nonterminal finish
    finishInside.1 (finishInside.2.trans terminalBound) radialSmall
    (fun time inside => (targetSmall time inside).trans ((min_le_right _ _).trans (min_le_left _ _)))
    (fun receiver below time inside => (followerSmall receiver below time inside).trans ((min_le_right _ _).trans (min_le_left _ _)))
    weight omegaWeight
  dsimp only at eliminatedData
  simp only [macroInvariant, selectedInvariant, remainingInvariant] at eliminatedData
  obtain ⟨allContinuous, _, finerContinuous, remainingContinuous, macroI, shapeI, allI, _, finerI, remainingI,
    literalBound, eliminatedBound⟩ := eliminatedData
  have macroData := macroResponse count phase dipoleAngle (prepared.enlargeCap macroCapBound) path drive nonterminal finish
    finishInside.1 (finishInside.2.trans terminalBound) radialSmall
    (fun time inside => (targetSmall time inside).trans ((min_le_right _ _).trans (min_le_right _ _))) weight omegaWeight
  dsimp only at macroData
  simp only [macroInvariant, selectedInvariant] at macroData
  have macroBound := macroData.2.2.2
  have closedData := closedResponse count phase dipoleAngle (prepared.enlargeCap closedCapBound) path drive nonterminal terminal
    terminalNonnegative terminalBound entry initialDistance direction entries extents coefficient coefficientPositive magnitude
    (by simpa only [rawInvariant] using profiles) finish finishInside
    (fun receiver below time inside => (followerSmall receiver below time inside).trans (min_le_left _ _)) weight omegaWeight sourceRates
  dsimp only at closedData
  simp only [weightedInvariant, remainingInvariant] at closedData
  have closedBound := closedData.2.2.2.2.2.2.2.2.2
  have driverIdentity : weighted (fun time => prepared.weightedMacroSourceState time drive) =
      location ^ 4 * weighted (fun time => prepared.macroSourceState time drive) := by
    dsimp only [weighted, CascadeSourcePreparedPair.weightedMacroSourceState]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    ring
  change weighted remaining ≤ 2 * known + (4 * responseConstant / weight) *
    weighted (fun time => prepared.weightedMacroSourceState time drive) at closedBound
  rw [driverIdentity] at closedBound
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have weightOne : 1 ≤ weight := omegaOne.trans omegaWeight
  have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
  have locationPositive : 0 < location := changed.location_pos _
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive (by linarith only [ratioBound]) _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive (by linarith only [ratioBound]) _).le
        (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]
    positivity
  let returnCoefficient := 4 * followerConstant * rho / (omega * location ^ 4)
  let driverCoefficient := (4 * responseConstant / weight) * location ^ 4
  have coefficientMacro : returnCoefficient * driverCoefficient * macroConstant =
      16 * followerConstant * responseConstant * macroConstant * rho / (omega * weight) := by
    dsimp only [returnCoefficient, driverCoefficient]
    (field_simp; ring)
  have coefficientFeedback : returnCoefficient * driverCoefficient * (macroConstant / weight) =
      16 * followerConstant * responseConstant * macroConstant * rho / (omega * weight ^ 2) := by
    dsimp only [returnCoefficient, driverCoefficient]
    (field_simp; ring)
  have smallOne : product * rho ≤ 1 := productSmall.le.trans (min_le_left _ _)
  have smallTolerance : product * rho ≤ tolerance / 2 := productSmall.le.trans (min_le_right _ _)
  have feedbackBound : returnCoefficient * driverCoefficient * (macroConstant / weight) ≤ 1 / 2 := by
    rw [coefficientFeedback]
    apply (div_le_iff₀ (mul_pos omegaPositive (sq_pos_of_pos weightPositive))).mpr
    have denominator : 1 ≤ omega * weight ^ 2 :=
      one_le_mul_of_one_le_of_one_le omegaOne (one_le_pow₀ weightOne)
    have halfSmall : 16 * followerConstant * responseConstant * macroConstant * rho ≤ 1 / 2 := by
      calc
        _ = (1 / 2 : ℝ) * (product * rho) := by dsimp only [product]; ring
        _ ≤ (1 / 2 : ℝ) * 1 := mul_le_mul_of_nonneg_left smallOne (by norm_num)
        _ = 1 / 2 := by ring
    exact halfSmall.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left denominator (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have shapeBound : 2 * (2 * eliminationMacro * eta + returnCoefficient * driverCoefficient * macroConstant) ≤ tolerance := by
    rw [coefficientMacro]
    have denominator : 1 ≤ omega * weight := one_le_mul_of_one_le_of_one_le omegaOne weightOne
    have numeratorNonnegative : 0 ≤ 32 * followerConstant * responseConstant * macroConstant * rho := by positivity
    have quotient := (div_le_self numeratorNonnegative denominator)
    have initialIdentity : 4 * eliminationMacro * eta = tolerance / 2 := by
      dsimp only [eta]
      (field_simp; ring)
    have expanded : 2 * (2 * eliminationMacro * eta +
        16 * followerConstant * responseConstant * macroConstant * rho / (omega * weight)) =
        4 * eliminationMacro * eta + 32 * followerConstant * responseConstant * macroConstant * rho / (omega * weight) := by ring
    rw [expanded, initialIdentity]
    dsimp only [product] at smallTolerance
    linarith only [quotient, smallTolerance]
  have allNonnegative : 0 ≤ weighted allForcing := intervalIntegral.integral_nonneg finishInside.1
    (fun time _ => mul_nonneg (Real.exp_pos _).le (by
      dsimp only [allForcing, CascadeSourcePreparedPair.selectedForeignForcing,
        CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm]
      positivity))
  have shapeNonnegative : 0 ≤ weighted shape := intervalIntegral.integral_nonneg finishInside.1
    (fun time _ => mul_nonneg (Real.exp_pos _).le (add_nonneg (abs_nonneg _) (abs_nonneg _)))
  have closedScaled : weighted remaining ≤ 2 * known + driverCoefficient * weighted (fun time => prepared.macroSourceState time drive) := by
    convert closedBound using 1; ring
  have returnNonnegative : 0 ≤ returnCoefficient := by dsimp only [returnCoefficient]; positivity
  have driverNonnegative : 0 ≤ driverCoefficient := by dsimp only [driverCoefficient]; positivity
  have scalar := mixed_closed_feedback_scalar allNonnegative shapeNonnegative returnNonnegative driverNonnegative
    eliminatedBound closedScaled macroBound feedbackBound shapeBound
  refine ⟨allContinuous, finerContinuous, remainingContinuous, macroI, shapeI, allI, finerI, remainingI, literalBound, ?_⟩
  change weighted allForcing ≤ tolerance * weighted shape + 4 * weighted finerForcing +
    (16 * followerConstant * rho / (omega * location ^ 4)) * known
  (convert scalar using 1; dsimp only [returnCoefficient]; ring)

end EulerNonuniqueness.Paper
