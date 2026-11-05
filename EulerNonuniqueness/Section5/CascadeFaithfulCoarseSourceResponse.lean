import EulerNonuniqueness.Section5.CascadeFiniteCoordinateLocalForeignHistory
import EulerNonuniqueness.Section5.CascadeActualFaithfulBoundaryMemory
import EulerNonuniqueness.General.RestartedCoupledCoarseVolterra

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_faithful_coarse_source_response :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
      ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∃ memoryConstant ≥ (1 : ℝ), ∃ radiusCoefficient ≥ (1 : ℝ),
      ∃ responseConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
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
        let changed : Scales := {scales with frequency := frequency}
        let omega := changed.omega (index.val + 1)
        let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
        let boundaryRadius := radiusCoefficient / (scaleRoot ^ 2 * omega ^ 2)
        let distance := fun time => ∑ patch : Fin 4,
          prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonBoundaryDistance
            (finProdFinEquiv (index, patch)) (patchSign patch * changed.amplitude * omega ^ 4) time boundaryRadius
            (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)
            (prepared.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)
        let size := prepared.finiteCoordinateSize graph coordinate lift index
        let forcing := prepared.finiteCoordinateForeignForcing index
        let physical := prepared.physicalForeignSourceForcing index
        let drive := fun time => omega * prepared.rawSourceCenteredState time index + physical time
        let rate := memoryConstant * (1 + omega * epsilon)
        let memory := fun time => memoryConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * drive current
        (ContinuousOn memory (Icc 0 path.stop) ∧ IntervalIntegrable memory volume 0 path.stop ∧
          memory 0 = 0 ∧ distance 0 = 0 ∧
          (∀ time ∈ Icc 0 path.stop, 0 ≤ memory time ∧ distance time ≤ memory time ∧
            (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤ memoryConstant * memory time) ∧
          ∀ start ∈ Icc 0 path.stop, ∀ time ∈ Icc start path.stop,
            memory time = Real.exp (rate * (time - start)) * memory start +
              memoryConstant * ∫ current in start..time,
                Real.exp (rate * (time - current)) * drive current) ∧
        ContinuousOn size (Icc 0 finish) ∧ ContinuousOn forcing (Icc 0 finish) ∧ ContinuousOn physical (Icc 0 finish) ∧
        IntervalIntegrable size volume 0 finish ∧ IntervalIntegrable memory volume 0 finish ∧
        IntervalIntegrable forcing volume 0 finish ∧ IntervalIntegrable physical volume 0 finish ∧
        size 0 = 0 ∧
        ∀ time ∈ Icc 0 finish,
          size time + memory time ≤ responseConstant * ∫ current in (0 : ℝ)..time,
            Real.exp (responseConstant * omega * (time - current)) * (forcing current + physical current) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, thresholdMax, thresholdPositive, thresholdEighth, coordinateCap, coordinateCapPositive, coordinateFactory⟩ :=
    exists_uniform_actual_finite_coordinate_local_foreign_history
  obtain ⟨geometryRadius, geometryPositive, _, geometryConstant, geometryOne, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨memoryCap, memoryPositive, memoryFactory⟩ := exists_uniform_actual_faithful_boundary_memory
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let cap := min coordinateCap (min memoryCap continuityCap)
  have capPositive : 0 < cap := lt_min coordinateCapPositive (lt_min memoryPositive continuityPositive)
  have coordinateCapBound : cap ≤ coordinateCap := min_le_left _ _
  have memoryCapBound : cap ≤ memoryCap := (min_le_right _ _).trans (min_le_left _ _)
  have continuityCapBound : cap ≤ continuityCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    thresholdMax, thresholdPositive, thresholdEighth, cap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨coordinateRadius, coordinatePositive, coordinateQuarter, coordinateConstant, coordinateOne, coordinates⟩ :=
    coordinateFactory factorPositive factorSmall
  obtain ⟨memoryConstant, memoryOne, radiusCoefficient, radiusCoefficientOne, rootMin, rootEight, memories⟩ :=
    memoryFactory factor factorPositive factorOne
  let radius := min coordinateRadius geometryRadius
  let combinedConstant := max (coordinateConstant * memoryConstant) (memoryConstant * geometryConstant)
  have memoryNonnegativeConstant : 0 ≤ memoryConstant := zero_le_one.trans memoryOne
  have geometryNonnegativeConstant : 0 ≤ geometryConstant := zero_le_one.trans geometryOne
  have coordinateNonnegativeConstant : 0 ≤ coordinateConstant := zero_le_one.trans coordinateOne
  have coordinateBelow : coordinateConstant ≤ combinedConstant :=
    (le_mul_of_one_le_right coordinateNonnegativeConstant memoryOne).trans (le_max_left _ _)
  have combinedOne : 1 ≤ combinedConstant := coordinateOne.trans coordinateBelow
  have combinedNonnegative : 0 ≤ combinedConstant := zero_le_one.trans combinedOne
  let responseConstant := 1 + 2 * combinedConstant
  have responseOne : 1 ≤ responseConstant := by dsimp only [responseConstant]; linarith only [combinedNonnegative]
  refine ⟨radius, lt_min coordinatePositive geometryPositive, (min_le_left _ _).trans coordinateQuarter,
    memoryConstant, memoryOne, radiusCoefficient, radiusCoefficientOne, responseConstant, responseOne,
    rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
    thresholdSmall referenceNonnegative boundaryOne orbit sectionTime
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdEighthBound : threshold ≤ 1 / 8 := thresholdSmall.trans thresholdEighth
  filter_upwards [coordinates scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative,
    memories scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
      thresholdEighthBound referenceNonnegative boundaryOne orbit sectionTime,
    geometries scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive (factorSmall.trans (by norm_num)) thresholdEighthBound referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    scales.eventually_cascade_physical_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighthBound referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_ge_atTop (max 1 (2 * memoryConstant))]
    with frequency coordinateEstimate memoryEstimate geometryEstimate coherence physicalEstimate frequencyLarge
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
  let rate := memoryConstant * (1 + omega * epsilon)
  let drive := fun time => omega * center time + physical time
  let memory := fun time => memoryConstant * ∫ current in (0 : ℝ)..time,
    Real.exp (rate * (time - current)) * drive current
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
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive
    (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have omegaNonnegative : 0 ≤ omega := zero_le_one.trans omegaOne
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have omegaEpsilonIdentity : omega * epsilon = 2 / (changed.amplitude * omega ^ 2) := by
    dsimp only [epsilon]
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
  have epsilonOne : epsilon ≤ 1 :=
    (le_mul_of_one_le_left epsilonNonnegative omegaOne).trans omegaEpsilonOne
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have rateOmega : rate ≤ omega := by
    have first := mul_le_mul_of_nonneg_left omegaEpsilonOne memoryNonnegativeConstant
    have second : 2 * memoryConstant ≤ omega :=
      ((le_max_right _ _).trans frequencyLarge).trans
        (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
    dsimp only [rate]
    linarith only [first, second]
  have rawNonnegative (time : ℝ) : 0 ≤ raw time := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have forcingNonnegative (time : ℝ) : 0 ≤ forcing time := by
    have locationPositive := changed.location_pos (index.val + 1)
    dsimp only [forcing, CascadeSourcePreparedPair.finiteCoordinateForeignForcing]
    positivity
  have memoryData := memoryEstimate count phase dipoleAngle prepared capPositive memoryCapBound path index
  have memoryContinuousFull : ContinuousOn memory (Icc 0 path.stop) := memoryData.1
  have memoryContinuous : ContinuousOn memory (Icc 0 finish) := memoryContinuousFull.mono subset
  have memoryInitial : memory 0 = 0 := memoryData.2.2.1
  have memoryBounds := memoryData.2.2.2.2.1
  have memoryNonnegative (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ memory time :=
    (memoryBounds time (subset inside)).1
  have rawMemory (time : ℝ) (inside : time ∈ Icc 0 finish) : raw time ≤ memoryConstant * memory time :=
    (memoryBounds time (subset inside)).2.2
  have coordinateBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      size time ≤ size 0 + combinedConstant * ∫ current in (0 : ℝ)..time,
        omega * (size current + epsilon * memory current) + forcing current := by
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
    rw [sizeInitial, zero_add]
    have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have lowerContinuous : ContinuousOn (fun current => omega * (size current + epsilon * raw current) + forcing current) (Icc 0 time) :=
      (continuousOn_const.mul ((sizeContinuous.mono prefixSubset).add
        (continuousOn_const.mul (rawContinuous.mono prefixSubset)))).add (forcingContinuous.mono prefixSubset)
    have upperContinuous : ContinuousOn (fun current => memoryConstant *
        (omega * (size current + epsilon * memory current) + forcing current)) (Icc 0 time) :=
      continuousOn_const.mul ((continuousOn_const.mul ((sizeContinuous.mono prefixSubset).add
        (continuousOn_const.mul (memoryContinuous.mono prefixSubset)))).add (forcingContinuous.mono prefixSubset))
    have comparison := intervalIntegral.integral_mono_on inside.1
      (lowerContinuous.intervalIntegrable_of_Icc (μ := volume) inside.1)
      (upperContinuous.intervalIntegrable_of_Icc (μ := volume) inside.1) (by
        intro current member
        have rawScaled := mul_le_mul_of_nonneg_left (rawMemory current (prefixSubset member))
          (mul_nonneg omegaNonnegative epsilonNonnegative)
        have sizeScaled := le_mul_of_one_le_left
          (mul_nonneg omegaNonnegative (sizeNonnegative current (prefixSubset member))) memoryOne
        have forceScaled := le_mul_of_one_le_left (forcingNonnegative current) memoryOne
        nlinarith only [rawScaled, sizeScaled, forceScaled])
    rw [intervalIntegral.integral_const_mul] at comparison
    have integralNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time,
        omega * (size current + epsilon * memory current) + forcing current :=
      intervalIntegral.integral_nonneg inside.1 (fun current member => by
        exact add_nonneg (mul_nonneg omegaNonnegative
          (add_nonneg (sizeNonnegative current (prefixSubset member))
            (mul_nonneg epsilonNonnegative (memoryNonnegative current (prefixSubset member))))) (forcingNonnegative current))
    calc
      size time ≤ coordinateConstant * ∫ current in (0 : ℝ)..time,
          omega * (size current + epsilon * raw current) + forcing current := literalActual
      _ ≤ coordinateConstant * (memoryConstant * ∫ current in (0 : ℝ)..time,
          omega * (size current + epsilon * memory current) + forcing current) :=
        mul_le_mul_of_nonneg_left comparison coordinateNonnegativeConstant
      _ = (coordinateConstant * memoryConstant) * ∫ current in (0 : ℝ)..time,
          omega * (size current + epsilon * memory current) + forcing current := by ring
      _ ≤ combinedConstant * ∫ current in (0 : ℝ)..time,
          omega * (size current + epsilon * memory current) + forcing current :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) integralNonnegative
  have memoryBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      memory time ≤ memory 0 * Real.exp (rate * (time - 0)) +
        combinedConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current) := by
    rw [memoryInitial, zero_mul, zero_add]
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
      have scaled := mul_le_mul_of_nonneg_left (add_le_add centered foreign) (Real.exp_pos (rate * (time - current))).le
      exact scaled.trans_eq (by ring))
    rw [intervalIntegral.integral_const_mul] at comparison
    have integralNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * (omega * size current + physical current) :=
      intervalIntegral.integral_nonneg inside.1 (fun current member => mul_nonneg (Real.exp_pos _).le
        (add_nonneg (mul_nonneg omegaNonnegative (sizeNonnegative current (prefixSubset member))) (physicalNonnegative current)))
    calc
      memory time = memoryConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * center current + physical current) := rfl
      _ ≤ memoryConstant * (geometryConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current)) :=
        mul_le_mul_of_nonneg_left comparison memoryNonnegativeConstant
      _ = (memoryConstant * geometryConstant) * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current) := by ring
      _ ≤ combinedConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (omega * size current + physical current) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) integralNonnegative
  have resolved := General.coupled_coarse_volterra_on_subinterval sizeContinuous memoryContinuous forcingContinuous physicalContinuous
    combinedNonnegative omegaNonnegative epsilonNonnegative epsilonOne rateNonnegative finishNonnegative
    sizeNonnegative memoryNonnegative (fun time _ => forcingNonnegative time) coordinateBound memoryBound
  refine ⟨lift, liftProperties, polar, memoryData, sizeContinuous, forcingContinuous, physicalContinuous,
    sizeContinuous.intervalIntegrable_of_Icc finishNonnegative, memoryContinuous.intervalIntegrable_of_Icc finishNonnegative,
    forcingContinuous.intervalIntegrable_of_Icc finishNonnegative, physicalContinuous.intervalIntegrable_of_Icc finishNonnegative,
    sizeInitial, ?_⟩
  have rateBound : rate + combinedConstant * (2 * omega) ≤ responseConstant * omega := by
    dsimp only [responseConstant]
    nlinarith only [rateOmega]
  have coefficientBound : combinedConstant ≤ responseConstant := by
    dsimp only [responseConstant]
    linarith only [combinedNonnegative]
  intro time inside
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have coarseKernel : Continuous (fun current : ℝ => Real.exp (responseConstant * omega * (time - current))) := by fun_prop
  have coarseI := (coarseKernel.continuousOn.mul ((forcingContinuous.add physicalContinuous).mono prefixSubset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have originalI := (resolved time inside).1
  have comparison := intervalIntegral.integral_mono_on inside.1 originalI coarseI (by
    intro current member
    have exponential := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right rateBound (sub_nonneg.mpr member.2))
    exact mul_le_mul_of_nonneg_right exponential (add_nonneg (forcingNonnegative current) (physicalNonnegative current)))
  have coarseNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time,
      Real.exp (responseConstant * omega * (time - current)) * (forcing current + physical current) :=
    intervalIntegral.integral_nonneg inside.1 (fun current _ => mul_nonneg (Real.exp_pos _).le
      (add_nonneg (forcingNonnegative current) (physicalNonnegative current)))
  have actual := (resolved time inside).2
  simp only [sizeInitial, memoryInitial, zero_add, zero_mul] at actual
  exact (actual.trans (mul_le_mul_of_nonneg_left comparison combinedNonnegative)).trans
    (mul_le_mul_of_nonneg_right coefficientBound coarseNonnegative)

end EulerNonuniqueness.Paper

