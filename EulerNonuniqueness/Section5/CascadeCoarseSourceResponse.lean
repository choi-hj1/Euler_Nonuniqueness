import EulerNonuniqueness.Section5.CascadeFiniteCoordinateLocalForeignHistory
import EulerNonuniqueness.Section5.CascadeRawSourceLocalForeignVolterra
import EulerNonuniqueness.Section5.CascadePhysicalForeignForcingContinuity
import EulerNonuniqueness.General.CoupledCoarseVolterra

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_coarse_source_response :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
      ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ threshold referenceConstant boundaryConstant : ℝ,
      threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
      ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish,
        |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
          |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
      ∃ lift : Fin 2 → ℝ → ℝ,
        (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
        (∀ side, ∀ time ∈ Icc 0 finish,
          positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
            (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
              Complex.exp (Complex.I * (lift side time : ℂ))) ∧
        let size := prepared.finiteCoordinateSize graph coordinate lift index
        let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
        let forcing := prepared.finiteCoordinateForeignForcing index
        let physical := prepared.physicalForeignSourceForcing index
        ContinuousOn size (Icc 0 finish) ∧ ContinuousOn raw (Icc 0 finish) ∧
        ContinuousOn forcing (Icc 0 finish) ∧ ContinuousOn physical (Icc 0 finish) ∧
        IntervalIntegrable size volume 0 finish ∧ IntervalIntegrable raw volume 0 finish ∧
        IntervalIntegrable forcing volume 0 finish ∧ IntervalIntegrable physical volume 0 finish ∧
        size 0 = 0 ∧
        ∀ time ∈ Icc 0 finish,
          size time + raw time ≤ constant * ∫ current in (0 : ℝ)..time,
            Real.exp (constant * ({scales with frequency := frequency} : Scales).omega (index.val + 1) * (time - current)) *
              (forcing current + physical current) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, thresholdMax, thresholdPositive, thresholdEighth, coordinateCap, coordinateCapPositive, coordinateFactory⟩ :=
    exists_uniform_actual_finite_coordinate_local_foreign_history
  obtain ⟨geometryRadius, geometryPositive, _, geometryConstant, geometryOne, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨rawCap, rawPositive, rawFactory⟩ := exists_uniform_actual_raw_source_local_foreign_volterra
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let cap := min coordinateCap (min rawCap continuityCap)
  have capPositive : 0 < cap := lt_min coordinateCapPositive (lt_min rawPositive continuityPositive)
  have coordinateCapBound : cap ≤ coordinateCap := min_le_left _ _
  have rawCapBound : cap ≤ rawCap := (min_le_right _ _).trans (min_le_left _ _)
  have continuityCapBound : cap ≤ continuityCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    thresholdMax, thresholdPositive, thresholdEighth, cap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨coordinateRadius, coordinatePositive, coordinateQuarter, coordinateConstant, coordinateOne, coordinates⟩ :=
    coordinateFactory factorPositive factorSmall
  obtain ⟨rawConstant, rawOne, rootMin, rootEight, raws⟩ := rawFactory factor factorPositive factorOne
  let radius := min coordinateRadius geometryRadius
  let combinedConstant := max coordinateConstant (rawConstant * geometryConstant)
  have combinedOne : 1 ≤ combinedConstant := coordinateOne.trans (le_max_left _ _)
  have combinedNonnegative : 0 ≤ combinedConstant := zero_le_one.trans combinedOne
  have rawNonnegativeConstant : 0 ≤ rawConstant := zero_le_one.trans rawOne
  have geometryNonnegativeConstant : 0 ≤ geometryConstant := zero_le_one.trans geometryOne
  refine ⟨radius, lt_min coordinatePositive geometryPositive, (min_le_left _ _).trans coordinateQuarter,
    1 + 2 * combinedConstant, by linarith only [combinedNonnegative], rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
    thresholdSmall referenceNonnegative boundaryOne orbit sectionTime
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdEighthBound : threshold ≤ 1 / 8 := thresholdSmall.trans thresholdEighth
  filter_upwards [coordinates scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative,
    raws scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
      thresholdEighthBound referenceNonnegative boundaryOne orbit sectionTime,
    geometries scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive (factorSmall.trans (by norm_num)) thresholdEighthBound referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    scales.eventually_cascade_physical_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighthBound referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)]
    with frequency coordinateEstimate rawEstimate geometryEstimate coherence physicalEstimate radii frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound small
  let changed : Scales := {scales with frequency := frequency}
  let coordinatePrepared := prepared.enlargeCap coordinateCapBound
  obtain ⟨lift, liftProperties, polar, sizeContinuous, sizeInitial, forcingContinuous, _, coordinateHistory⟩ :=
    coordinateEstimate count phase dipoleAngle coordinatePrepared path index nonterminal finish finishNonnegative finishBound
      (fun time inside => (small time inside).trans (min_le_left _ _))
  have coordinateBudgetIdentity : coordinatePrepared.rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances
      dsimp only [coordinatePrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  let size := prepared.finiteCoordinateSize graph coordinate lift index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let center := fun time => prepared.rawSourceCenteredState time index
  let forcing := prepared.finiteCoordinateForeignForcing index
  let physical := prepared.physicalForeignSourceForcing index
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let rate := rawConstant * omega * epsilon
  change ContinuousOn size (Icc 0 finish) at sizeContinuous
  change size 0 = 0 at sizeInitial
  change ContinuousOn forcing (Icc 0 finish) at forcingContinuous
  obtain ⟨geometryLift, geometryProperties, geometryPolar, _, _, geometryNonnegative, geometryBounds⟩ :=
    geometryEstimate prepared path index nonterminal finish finishNonnegative finishBound
      (fun time inside => (small time inside).trans (min_le_right _ _))
  have sizeEquality := (coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans ((min_le_left _ _).trans coordinateQuarter))
    geometryLift lift (fun side => (geometryProperties side).1.continuousOn)
    (fun side => (liftProperties side).1.continuousOn)
    (fun side => (geometryProperties side).2.trans (liftProperties side).2.symm) geometryPolar polar).2.2 graph coordinate
  have sizeNonnegative (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ size time := by
    exact (geometryNonnegative time).trans_eq (sizeEquality inside)
  have centerBound (time : ℝ) (inside : time ∈ Icc 0 finish) : center time ≤ geometryConstant * size time := by
    have actual := (geometryBounds time inside).1
    rw [sizeEquality inside] at actual
    exact actual
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum _
    (fun patch _ => ((stateContinuity prepared capPositive continuityCapBound path index).1 patch).mono subset)
  have centerContinuous : ContinuousOn center (Icc 0 finish) :=
    (stateContinuity prepared capPositive continuityCapBound path index).2.1.mono subset
  obtain ⟨_, physicalContinuousFull, physicalNonnegative, _⟩ := physicalEstimate count phase dipoleAngle prepared path index
  have physicalContinuous : ContinuousOn physical (Icc 0 finish) := physicalContinuousFull.mono subset
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive
    (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have omegaNonnegative : 0 ≤ omega := zero_le_one.trans omegaOne
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have epsilonOne : epsilon ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos (changed.length_pos _))).mpr
    have bound := (radii (index.val + 1)).le
    change changed.radius (index.val + 1) ≤ 1 * changed.length (index.val + 1) at bound
    exact pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le
      (by simpa only [one_mul] using bound) 2
  have rawNonnegative (time : ℝ) : 0 ≤ raw time := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have forcingNonnegative (time : ℝ) : 0 ≤ forcing time := by
    have locationPositive := changed.location_pos (index.val + 1)
    dsimp only [forcing, CascadeSourcePreparedPair.finiteCoordinateForeignForcing]
    positivity
  let rawPrepared := prepared.enlargeCap rawCapBound
  obtain ⟨rateNonnegative, rateOne, _, _, _, rawHistory⟩ :=
    rawEstimate count phase dipoleAngle rawPrepared path index finish finishNonnegative finishBound
  have rawBudgetIdentity : rawPrepared.rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances
      dsimp only [rawPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have rawCenterIdentity : rawPrepared.rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source
    with_reducible_and_instances
      dsimp only [rawPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawFirstIdentity : rawPrepared.referenceWitness.trajectory.movingFamily = prepared.referenceWitness.trajectory.movingFamily := rfl
  have rawSecondIdentity : rawPrepared.trajectory.movingFamily = prepared.trajectory.movingFamily := rfl
  change 0 ≤ rate at rateNonnegative
  change rate ≤ 1 at rateOne
  let opposite := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
        (changed.radius (index.val + 1)) (power + 1) time -
      prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch)
        (changed.radius (index.val + 1)) (power + 1) time‖
  have oppositeIdentity : opposite = physical := by
    funext time
    dsimp only [opposite, physical, CascadeSourcePreparedPair.physicalForeignSourceForcing]
    apply Finset.sum_congr rfl
    intro patch _
    apply tsum_congr
    intro power
    exact congrArg (fun value : ℝ => (96 : ℝ) ^ (power + 1) * value) (norm_sub_rev _ _)
  have literalRawHistory (time : ℝ) (inside : time ∈ Icc 0 finish) :
      raw time ≤ rawConstant * ∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * (omega * center current + physical current) := by
    have actual := rawHistory time inside
    dsimp only at actual
    simp only [rawBudgetIdentity, rawCenterIdentity, rawFirstIdentity, rawSecondIdentity] at actual
    change raw time ≤ rawConstant * ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * (omega * center current + opposite current) at actual
    rw [oppositeIdentity] at actual
    exact actual
  have coordinateBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      size time ≤ combinedConstant * ∫ current in (0 : ℝ)..time,
        omega * (size current + epsilon * raw current) + forcing current := by
    have actual := coordinateHistory time inside
    have integralIdentity : (∫ current in (0 : ℝ)..time,
        omega * (coordinatePrepared.finiteCoordinateSize graph coordinate lift index current +
          epsilon * ∑ patch : Fin 4, coordinatePrepared.rawSourceShapeBudget current index patch) +
            coordinatePrepared.finiteCoordinateForeignForcing index current) =
        ∫ current in (0 : ℝ)..time, omega * (size current + epsilon * raw current) + forcing current := by
      apply intervalIntegral.integral_congr
      intro current _
      exact congrArg (fun value : ℝ => omega * (size current + epsilon * value) + forcing current)
        (congrArg (fun budget : ℝ → Fin count → Fin 4 → ℝ => ∑ patch : Fin 4, budget current index patch) coordinateBudgetIdentity)
    have literalActual : size time ≤ coordinateConstant * ∫ current in (0 : ℝ)..time,
        omega * (size current + epsilon * raw current) + forcing current :=
      actual.trans_eq (congrArg (fun value : ℝ => coordinateConstant * value) integralIdentity)
    have integralNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time,
        omega * (size current + epsilon * raw current) + forcing current :=
      intervalIntegral.integral_nonneg inside.1 (fun current member =>
        add_nonneg (mul_nonneg omegaNonnegative (add_nonneg (sizeNonnegative current ⟨member.1, member.2.trans inside.2⟩)
          (mul_nonneg epsilonNonnegative (rawNonnegative current)))) (forcingNonnegative current))
    exact literalActual.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) integralNonnegative)
  have rawBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      raw time ≤ combinedConstant * ∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * (omega * size current + physical current) := by
    have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have kernelContinuous : Continuous (fun current : ℝ => Real.exp (rate * (time - current))) := by fun_prop
    have lowerIntegrable : IntervalIntegrable (fun current => Real.exp (rate * (time - current)) *
        (omega * center current + physical current)) volume 0 time := (kernelContinuous.continuousOn.mul
      ((continuousOn_const.mul (centerContinuous.mono prefixSubset)).add (physicalContinuous.mono prefixSubset))).intervalIntegrable_of_Icc (μ := volume) inside.1
    have upperIntegrable : IntervalIntegrable (fun current => geometryConstant * (Real.exp (rate * (time - current)) *
        (omega * size current + physical current))) volume 0 time := ((kernelContinuous.continuousOn.mul
      ((continuousOn_const.mul (sizeContinuous.mono prefixSubset)).add (physicalContinuous.mono prefixSubset))).intervalIntegrable_of_Icc
        (μ := volume) inside.1).const_mul geometryConstant
    have comparison := intervalIntegral.integral_mono_on inside.1 lowerIntegrable upperIntegrable (by
      intro current member
      have centered := mul_le_mul_of_nonneg_left (centerBound current (prefixSubset member)) omegaNonnegative
      have foreign := le_mul_of_one_le_left (physicalNonnegative current) geometryOne
      have point := add_le_add centered foreign
      have scaled := mul_le_mul_of_nonneg_left point (Real.exp_pos (rate * (time - current))).le
      exact scaled.trans_eq (by ring))
    rw [intervalIntegral.integral_const_mul] at comparison
    have integralNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * (omega * size current + physical current) :=
      intervalIntegral.integral_nonneg inside.1 (fun current member => mul_nonneg (Real.exp_pos _).le
        (add_nonneg (mul_nonneg omegaNonnegative (sizeNonnegative current (prefixSubset member))) (physicalNonnegative current)))
    calc
      raw time ≤ rawConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * center current + physical current) := literalRawHistory time inside
      _ ≤ rawConstant * (geometryConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current)) :=
        mul_le_mul_of_nonneg_left comparison rawNonnegativeConstant
      _ = (rawConstant * geometryConstant) * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current) := by rw [mul_assoc]
      _ ≤ combinedConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) integralNonnegative
  have response := General.coupled_coarse_volterra_on_Icc sizeContinuous rawContinuous forcingContinuous physicalContinuous
    combinedNonnegative omegaOne epsilonNonnegative epsilonOne rateNonnegative rateOne finishNonnegative
    sizeNonnegative (fun time _ => rawNonnegative time) (fun time _ => forcingNonnegative time)
    (fun time _ => physicalNonnegative time) coordinateBound rawBound
  refine ⟨lift, liftProperties, polar, sizeContinuous, rawContinuous, forcingContinuous, physicalContinuous,
    sizeContinuous.intervalIntegrable_of_Icc finishNonnegative, rawContinuous.intervalIntegrable_of_Icc finishNonnegative,
    forcingContinuous.intervalIntegrable_of_Icc finishNonnegative, physicalContinuous.intervalIntegrable_of_Icc finishNonnegative,
    sizeInitial, response⟩

end EulerNonuniqueness.Paper
