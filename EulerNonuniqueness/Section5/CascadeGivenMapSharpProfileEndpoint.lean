import EulerNonuniqueness.Section5.CascadeGivenMapShapeProfileEndpoint
import EulerNonuniqueness.Section5.CascadeSharpStateFiniteCoordinateBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_given_map_sharp_profile_endpoint
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha → ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant boundaryConstant : ℝ}, threshold ≤ thresholdMax →
    0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∃ lift : Fin 2 → ℝ → ℝ,
    (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (lift side time : ℂ))) ∧
    let changed : Scales := {scales with frequency := frequency}
    let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let shape := fun time =>
      |(referenceStraightenedShape first graph coordinate index time).1 -
        (referenceStraightenedShape second graph coordinate index time).1| +
      |(referenceStraightenedShape first graph coordinate index time).2 -
        (referenceStraightenedShape second graph coordinate index time).2|
    let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
    let state := fun time => prepared.finiteCoordinateSize graph coordinate lift index time + raw time
    let sharp := fun time => prepared.rawSourceCenteredState time index +
      ‖relativeNormalizedFirstMoment changed first second index time‖ +
      ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / changed.location (index.val + 1) + raw time
    let forcing := fun time => prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time
    ContinuousOn state (Icc 0 finish) ∧ state 0 = 0 ∧
    IntervalIntegrable (fun time => Real.exp (-growth * time) * forcing time) volume 0 finish ∧
    ∀ origin magnitude action : ℝ, 0 ≤ magnitude → 0 ≤ action →
      (∀ time ∈ Icc 0 finish, shape time ≤ magnitude * Real.exp (growth * (time - origin))) →
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * forcing time) ≤ action * Real.exp (-growth * origin) →
      ∀ time ∈ Icc 0 finish,
        state time ≤ constant * (magnitude + action) * Real.exp (growth * (time - origin)) ∧
        sharp time ≤ constant * (magnitude + action) * Real.exp (growth * (time - origin)) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, profiles⟩ :=
    exists_uniform_actual_given_map_shape_profile_endpoint graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨geometryRadius, geometryPositive, geometryQuarter, _, _, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨sharpRadius, sharpPositive, _, sharpConstant, sharpOne, sharpEstimates⟩ :=
    exists_uniform_actual_sharp_state_finite_coordinate_bound graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨profileRadius, profilePositive, _, profileConstant, profileOne, rootMin, rootEight, factory⟩ :=
    profiles factor factorPositive factorSmall
  let radius := min geometryRadius (min sharpRadius profileRadius)
  let constant := (sharpConstant + 1) * profileConstant
  have sharpNonnegative : 0 ≤ sharpConstant := zero_le_one.trans sharpOne
  have profileNonnegative : 0 ≤ profileConstant := zero_le_one.trans profileOne
  have constantOne : 1 ≤ constant := by
    dsimp only [constant]
    nlinarith only [profileOne, mul_nonneg sharpNonnegative profileNonnegative]
  have profileBelow : profileConstant ≤ constant := by
    dsimp only [constant]
    nlinarith only [mul_nonneg sharpNonnegative profileNonnegative]
  have sharpProfileBelow : sharpConstant * profileConstant ≤ constant := by
    dsimp only [constant]
    nlinarith only [profileNonnegative]
  refine ⟨radius, lt_min geometryPositive (lt_min sharpPositive profilePositive),
    (min_le_left _ _).trans geometryQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive orbit sectionTime
    threshold referenceConstant boundaryConstant thresholdBound referenceNonnegative boundaryOne
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [factory scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive orbit sectionTime
      thresholdBound referenceNonnegative boundaryOne,
    geometries scales amplitudePositive ratioBound alphaPositive rootPositive (zero_le_one.trans boundaryOne)
      factorPositive factorEighth thresholdSmall referenceNonnegative,
    sharpEstimates scales amplitudePositive ratioBound alphaPositive rootPositive (zero_le_one.trans boundaryOne)
      factorPositive factorEighth thresholdSmall referenceNonnegative]
    with frequency profileEstimate geometryEstimate sharpEstimate
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound small
  obtain ⟨lift, liftContinuous, liftPolar, _, _, _, _⟩ := geometryEstimate prepared path index nonterminal finish
    finishNonnegative finishBound (fun time inside => (small time inside).trans (min_le_left _ _))
  have profileData := profileEstimate count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans ((min_le_right _ _).trans (min_le_right _ _)))
    lift (fun side => (liftContinuous side).1.continuousOn) (fun side => (liftContinuous side).2) liftPolar
  have sharpData := sharpEstimate prepared path index nonterminal finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans ((min_le_right _ _).trans (min_le_left _ _)))
    lift (fun side => (liftContinuous side).1.continuousOn) (fun side => (liftContinuous side).2) liftPolar
  obtain ⟨sizeContinuous, sizeInitial, rawContinuous, _, forcingI, endpoint⟩ := profileData
  have rawInitial : (∑ patch : Fin 4, prepared.rawSourceShapeBudget 0 index patch) = 0 := by
    apply Finset.sum_eq_zero
    intro patch _
    have rawEqual : prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) 0 =
        prepared.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) 0 := by
      simp only [MovingCentroidGaugeTrajectory.spectralCoordinate,
        prepared.referenceWitness.trajectory.initial_identity, prepared.trajectory.initial_identity]
      rfl
    with_reducible_and_instances
      simp only [CascadeSourcePreparedPair.rawSourceShapeBudget, rawEqual, sub_self, norm_zero, mul_zero, add_zero]
  refine ⟨lift, liftContinuous, liftPolar, sizeContinuous.add rawContinuous, ?_, forcingI, ?_⟩
  · simp only [sizeInitial, rawInitial, add_zero]
  intro origin magnitude action magnitudeNonnegative actionNonnegative shapeProfile forcingBound time inside
  have stateBound := endpoint origin magnitude action magnitudeNonnegative actionNonnegative shapeProfile forcingBound time inside
  have sharpBound := (sharpData.2.2 time inside).trans (mul_le_mul_of_nonneg_left stateBound sharpNonnegative)
  have budgetNonnegative : 0 ≤ (magnitude + action) * Real.exp
      ((2 * Real.sqrt 2 * ({scales with frequency := frequency} : Scales).omega (index.val + 1)) * (time - origin)) := by positivity
  refine ⟨stateBound.trans ?_, sharpBound.trans ?_⟩
  · convert mul_le_mul_of_nonneg_right profileBelow budgetNonnegative using 1 <;> ring
  · convert mul_le_mul_of_nonneg_right sharpProfileBelow budgetNonnegative using 1 <;> ring

end EulerNonuniqueness.Paper
