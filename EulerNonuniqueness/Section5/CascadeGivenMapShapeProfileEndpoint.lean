import EulerNonuniqueness.Section5.CascadeGivenMapNeutralOriginalHistory
import EulerNonuniqueness.Section5.CascadeFiniteCoordinateShapeArbitraryWeightReturn
import EulerNonuniqueness.Section5.CascadeFaithfulBoundaryMemoryWeightedReturn
import EulerNonuniqueness.General.TwoRateExponentialResponse

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_given_map_shape_profile_endpoint
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha → ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant boundaryConstant : ℝ}, threshold ≤ thresholdMax → 0 ≤ referenceConstant →
    1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∀ lift : Fin 2 → ℝ → ℝ, (∀ side, ContinuousOn (lift side) (Icc 0 finish)) →
    (∀ side, lift side 0 = phase (index.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
          Complex.exp (Complex.I * (lift side time : ℂ))) →
    let changed : Scales := {scales with frequency := frequency}
    let omega := changed.omega (index.val + 1)
    let growth := 2 * Real.sqrt 2 * omega
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let shape := fun time =>
      |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
      |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2|
    let size := prepared.finiteCoordinateSize graph coordinate lift index
    let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
    let forcing := fun time => prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time
    ContinuousOn size (Icc 0 finish) ∧ size 0 = 0 ∧ ContinuousOn raw (Icc 0 finish) ∧ ContinuousOn forcing (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-growth * time) * forcing time) volume 0 finish ∧
    ∀ origin magnitude action : ℝ, 0 ≤ magnitude → 0 ≤ action →
      (∀ time ∈ Icc 0 finish, shape time ≤ magnitude * Real.exp (growth * (time - origin))) →
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * forcing time) ≤ action * Real.exp (-growth * origin) →
      ∀ time ∈ Icc 0 finish,
        size time + raw time ≤ constant * (magnitude + action) * Real.exp (growth * (time - origin)) := by
  obtain ⟨historyThreshold, historyPositive, historyEighth, historyCap, historyCapPositive, histories⟩ :=
    exists_uniform_actual_given_map_neutral_original_history graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨weightThreshold, weightPositive, _, weightCap, weightCapPositive, weights⟩ :=
    exists_uniform_actual_finite_coordinate_shape_arbitrary_weight_return graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨memoryCap, memoryCapPositive, memories⟩ := exists_uniform_actual_faithful_boundary_memory_weighted_return
  obtain ⟨stateCap, stateCapPositive, states⟩ := exists_uniform_actual_source_state_continuity
  obtain ⟨geometryRadius, geometryPositive, _, geometryConstant, geometryOne, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  let rawCap := min historyCap (min weightCap (min memoryCap stateCap))
  have capPositive : 0 < rawCap := lt_min historyCapPositive (lt_min weightCapPositive (lt_min memoryCapPositive stateCapPositive))
  have capHistory : rawCap ≤ historyCap := min_le_left _ _
  have capWeight : rawCap ≤ weightCap := (min_le_right _ _).trans (min_le_left _ _)
  have capMemory : rawCap ≤ memoryCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have capState : rawCap ≤ stateCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let thresholdMax := min historyThreshold weightThreshold
  have thresholdEighth : thresholdMax ≤ 1 / 8 := (min_le_left _ _).trans historyEighth
  refine ⟨thresholdMax, lt_min historyPositive weightPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  obtain ⟨historyRadius, historyRadiusPositive, historyQuarter, historyConstant, historyOne, historyRoot, historyEight, historyFactory⟩ :=
    histories factor factorPositive factorSmall
  obtain ⟨weightRadius, weightRadiusPositive, _, weightConstant, weightOne, weightRoot, _, weightFactory⟩ :=
    weights factor factorPositive factorSmall
  obtain ⟨memoryConstant, memoryOne, _, _, memoryRoot, _, memoryFactory⟩ :=
    memories factor factorPositive factorOne
  let bound := 1 + historyConstant + weightConstant + memoryConstant + geometryConstant
  have boundOne : 1 ≤ bound := by dsimp only [bound]; linarith only [historyOne, weightOne, memoryOne, geometryOne]
  have boundNonnegative : 0 ≤ bound := zero_le_one.trans boundOne
  have historyBelow : historyConstant ≤ bound := by dsimp only [bound]; linarith only [weightOne, memoryOne, geometryOne]
  have weightBelow : weightConstant ≤ bound := by dsimp only [bound]; linarith only [historyOne, memoryOne, geometryOne]
  have memoryBelow : memoryConstant ≤ bound := by dsimp only [bound]; linarith only [historyOne, weightOne, geometryOne]
  have geometryBelow : geometryConstant ≤ bound := by dsimp only [bound]; linarith only [historyOne, weightOne, memoryOne]
  let joint := (bound + 2 * bound ^ 4 + bound ^ 3) + (bound + 3 * bound ^ 3)
  have jointNonnegative : 0 ≤ joint := by dsimp only [joint]; positivity
  let constant := 1 + joint * (bound + 1)
  have constantOne : 1 ≤ constant := by dsimp only [constant]; exact le_add_of_nonneg_right (mul_nonneg jointNonnegative (by positivity))
  let radius := min historyRadius (min weightRadius geometryRadius)
  let rootMin := max historyRoot (max weightRoot memoryRoot)
  have rootEight : 8 ≤ rootMin := historyEight.trans (le_max_left _ _)
  refine ⟨radius, lt_min historyRadiusPositive (lt_min weightRadiusPositive geometryPositive),
    (min_le_left _ _).trans historyQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive orbit sectionTime threshold referenceConstant boundaryConstant thresholdBound referenceNonnegative boundaryOne
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [historyFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      ((le_max_left _ _).trans rootLarge) boundaryOne (thresholdBound.trans (min_le_left _ _)) referenceNonnegative,
    weightFactory scales scaleRoot ((le_max_left _ _).trans ((le_max_right _ _).trans rootLarge))
      amplitudeIdentity ratioBound alphaPositive orbit sectionTime (thresholdBound.trans (min_le_right _ _)) referenceNonnegative boundaryOne,
    memoryFactory scales scaleRoot ((le_max_right _ _).trans ((le_max_right _ _).trans rootLarge))
      amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant thresholdSmall referenceNonnegative boundaryOne orbit sectionTime,
    geometries scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive factorEighth thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    scales.eventually_cascade_physical_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_ge_atTop (1 : ℝ)]
    with frequency historyEstimate weightEstimate memoryEstimate geometryEstimate coherence physicalEstimate frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound small lift liftContinuous liftInitial polar
  have rawInvariant {largerCap : ℝ} (larger : rawCap ≤ largerCap) :
      (prepared.enlargeCap larger).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have sizeInvariant {largerCap : ℝ} (larger : rawCap ≤ largerCap) :
      (prepared.enlargeCap larger).finiteCoordinateSize = prepared.finiteCoordinateSize := by
    funext graph coordinate lift source time
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.finiteCoordinateSize]
  have forcingInvariant {largerCap : ℝ} (larger : rawCap ≤ largerCap) :
      (prepared.enlargeCap larger).finiteCoordinateForeignForcing = prepared.finiteCoordinateForeignForcing := rfl
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let size := prepared.finiteCoordinateSize graph coordinate lift index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let centered := fun time => prepared.rawSourceCenteredState time index
  let shape := fun time =>
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).1 -
      (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).2 -
      (referenceStraightenedShape prepared.reference graph coordinate index time).2|
  let foreign := prepared.finiteCoordinateForeignForcing index
  let physical := prepared.physicalForeignSourceForcing index
  let forcing := fun time => foreign time + physical time
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let rate := memoryConstant * (1 + omega * epsilon)
  let memory := fun time => memoryConstant * ∫ current in (0 : ℝ)..time,
    Real.exp (rate * (time - current)) * (omega * centered current + physical current)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have omegaNonnegative : 0 ≤ omega := omegaPositive.le
  have lengthPositive := changed.length_pos (index.val + 1)
  have locationPositive := changed.location_pos (index.val + 1)
  have historyData := historyEstimate count phase dipoleAngle (prepared.enlargeCap capHistory) path index nonterminal finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans (min_le_left _ _)) lift liftContinuous liftInitial polar
  simp only [rawInvariant, sizeInvariant, forcingInvariant] at historyData
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at historyData
  obtain ⟨sizeContinuous, sizeInitial, foreignContinuous, _, budgetIntegrable, history⟩ := historyData
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum _
    (fun patch _ => ((states prepared capPositive capState path index).1 patch).mono subset)
  have physicalContinuous := (physicalEstimate count phase dipoleAngle prepared path index).2.1.mono subset
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) := foreignContinuous.add physicalContinuous
  obtain ⟨geometryLift, geometryProperties, geometryPolar, _, _, _, geometryBounds⟩ :=
    geometryEstimate prepared path index nonterminal finish finishNonnegative finishBound
      (fun time inside => (small time inside).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have sizeEquality := (coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans ((min_le_left _ _).trans historyQuarter)) geometryLift lift
    (fun side => (geometryProperties side).1.continuousOn) liftContinuous
    (fun side => (geometryProperties side).2.trans (liftInitial side).symm) geometryPolar polar).2.2 graph coordinate
  have centeredBound (time : ℝ) (inside : time ∈ Icc 0 finish) : centered time ≤ bound * size time := by
    have actual := (geometryBounds time inside).1
    rw [sizeEquality inside] at actual
    exact actual.trans (mul_le_mul_of_nonneg_right geometryBelow (by dsimp only [size, CascadeSourcePreparedPair.finiteCoordinateSize]; positivity))
  have sizeNonnegative (time : ℝ) : 0 ≤ size time := by dsimp only [size, CascadeSourcePreparedPair.finiteCoordinateSize]; positivity
  have rawNonnegative (time : ℝ) : 0 ≤ raw time := by
    apply Finset.sum_nonneg; intro patch _; dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
  have foreignNonnegative (time : ℝ) : 0 ≤ foreign time := by
    dsimp only [foreign, CascadeSourcePreparedPair.finiteCoordinateForeignForcing]; positivity
  have forcingNonnegative (time : ℝ) : 0 ≤ forcing time := add_nonneg (foreignNonnegative time) (prepared.physicalForeignSourceForcing_nonneg index time)
  have memoryData := memoryEstimate count phase dipoleAngle prepared capPositive capMemory path index
  have memoryContinuous : ContinuousOn memory (Icc 0 finish) := memoryData.1.1.mono subset
  have memoryNonnegative (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ memory time := (memoryData.1.2.2.2.2.1 time (subset inside)).1
  have rawMemory (time : ℝ) (inside : time ∈ Icc 0 finish) : raw time ≤ bound * memory time :=
    (memoryData.1.2.2.2.2.1 time (subset inside)).2.2.trans (mul_le_mul_of_nonneg_right memoryBelow (memoryNonnegative time inside))
  have rateOmega : rate ≤ omega := memoryData.2.2.1.trans (by linarith only [omegaNonnegative])
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have epsilonOne : epsilon ≤ 1 := by
    have lower : omega * epsilon ≤ rate := by
      have scaled := le_mul_of_one_le_left (show 0 ≤ 1 + omega * epsilon by positivity) memoryOne
      dsimp only [rate]; linarith only [scaled]
    exact (mul_le_mul_left omegaPositive).mp (by simpa only [mul_one] using lower.trans rateOmega)
  have lambdaGap : omega < growth := by
    have rootTwo : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    dsimp only [growth]; nlinarith only [omegaPositive, mul_nonneg omegaNonnegative (sub_nonneg.mpr rootTwo)]
  have weightedContinuous (weight : ℝ) : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have sourceI := ((weightedContinuous growth).continuousOn.mul forcingContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  refine ⟨sizeContinuous, sizeInitial, rawContinuous, forcingContinuous, sourceI, ?_⟩
  intro origin magnitude action magnitudeNonnegative actionNonnegative profile sourceBudget time inside
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have prefixSet : uIcc (0 : ℝ) time ⊆ uIcc 0 finish := by rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]; exact prefixSubset
  let weighted := fun function : ℝ → ℝ => ∫ current in (0 : ℝ)..time, Real.exp (-omega * current) * function current
  let kernel := fun current => Real.exp (omega * (time - current))
  have kernelContinuous : Continuous kernel := by dsimp only [kernel]; fun_prop
  have extract (function : ℝ → ℝ) : (∫ current in (0 : ℝ)..time, kernel current * function current) =
      Real.exp (omega * time) * weighted function := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro current _
    dsimp only [kernel, weighted]
    rw [← mul_assoc, ← Real.exp_add]; congr 2; ring
  have actualWeighted := weightEstimate count phase dipoleAngle (prepared.enlargeCap capWeight) path index nonterminal time inside.1
    (inside.2.trans finishBound) (fun current member => (small current (prefixSubset member)).trans ((min_le_right _ _).trans (min_le_left _ _)))
    lift (fun side => (liftContinuous side).mono prefixSubset) liftInitial (fun side current member => polar side current (prefixSubset member)) omega le_rfl
  simp only [sizeInvariant, forcingInvariant] at actualWeighted
  dsimp only [CascadeSourcePreparedPair.enlargeCap] at actualWeighted
  rw [← prepared.referenceIdentity] at actualWeighted
  change IntervalIntegrable (fun current => Real.exp (-omega * current) * size current) volume 0 time ∧
    IntervalIntegrable (fun current => Real.exp (-omega * current) * shape current) volume 0 time ∧
    IntervalIntegrable (fun current => Real.exp (-omega * current) * forcing current) volume 0 time ∧
    weighted size ≤ weightConstant * weighted shape + (weightConstant / omega) * weighted forcing at actualWeighted
  have memoryWeighted := memoryData.2.2.2 time (subset inside) omega le_rfl
  have nonnegative (function : ℝ → ℝ) (nonnegative : ∀ current ∈ Icc 0 time, 0 ≤ function current) : 0 ≤ weighted function :=
    intervalIntegral.integral_nonneg inside.1 (fun current member => mul_nonneg (Real.exp_pos _).le (nonnegative current member))
  have sizeIntegralNonnegative := nonnegative size (fun current _ => sizeNonnegative current)
  have sourceIntegralNonnegative := nonnegative forcing (fun current _ => forcingNonnegative current)
  have shapeIntegralNonnegative := nonnegative shape (fun current _ => by dsimp only [shape]; positivity)
  have centerComparison := intervalIntegral.integral_mono_on inside.1 memoryWeighted.2.1
    (actualWeighted.1.const_mul bound) (fun current member => (mul_le_mul_of_nonneg_left
      (centeredBound current (prefixSubset member)) (Real.exp_pos _).le).trans_eq (by ring))
  rw [intervalIntegral.integral_const_mul] at centerComparison
  have physicalComparison := intervalIntegral.integral_mono_on inside.1 memoryWeighted.2.2.1 actualWeighted.2.2.1
    (fun current _ => mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (foreignNonnegative current)) (Real.exp_pos _).le)
  have memoryIntegralBound : omega * weighted memory ≤ 2 * bound ^ 2 * (omega * weighted size) + 2 * bound * weighted forcing := by
    have scaled := mul_le_mul_of_nonneg_left memoryWeighted.2.2.2 omegaNonnegative
    have first := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left centerComparison omegaNonnegative) physicalComparison) (show 0 ≤ 2 * memoryConstant by positivity)
    have second := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left memoryBelow (by norm_num : (0 : ℝ) ≤ 2))
      (show 0 ≤ bound * (omega * weighted size) + weighted forcing by positivity)
    have identity : omega * (2 * memoryConstant / omega * (omega * weighted centered + weighted physical)) =
      2 * memoryConstant * (omega * weighted centered + weighted physical) := by field_simp
    rw [identity] at scaled
    nlinarith only [scaled, first, second]
  have sizeIntegralBound : omega * weighted size ≤ bound * (omega * weighted shape) + bound * weighted forcing := by
    have scaled := mul_le_mul_of_nonneg_left actualWeighted.2.2.2 omegaNonnegative
    have identity : omega * (weightConstant * weighted shape + weightConstant / omega * weighted forcing) =
      weightConstant * (omega * weighted shape) + weightConstant * weighted forcing := by field_simp; ring
    rw [identity] at scaled
    exact scaled.trans (add_le_add (mul_le_mul_of_nonneg_right weightBelow (by positivity))
      (mul_le_mul_of_nonneg_right weightBelow sourceIntegralNonnegative))
  let upper := fun current => omega * size current + bound * omega * memory current + forcing current
  have upperContinuous : ContinuousOn upper (Icc 0 time) :=
    ((continuousOn_const.mul (sizeContinuous.mono prefixSubset)).add (continuousOn_const.mul (memoryContinuous.mono prefixSubset))).add
      (forcingContinuous.mono prefixSubset)
  have upperNonnegative (current : ℝ) (member : current ∈ Icc 0 time) : 0 ≤ upper current := by
    have sizePositive := sizeNonnegative current
    have memoryPositive := memoryNonnegative current (prefixSubset member)
    have forcingPositive := forcingNonnegative current
    dsimp only [upper]; positivity
  have upperIdentity : (∫ current in (0 : ℝ)..time, kernel current * upper current) =
      Real.exp (omega * time) * (omega * weighted size + bound * omega * weighted memory + weighted forcing) := by
    rw [extract]
    dsimp only [weighted, upper]
    simp_rw [mul_add, mul_left_comm (Real.exp (-omega * _)) omega, mul_left_comm (Real.exp (-omega * _)) (bound * omega)]
    rw [intervalIntegral.integral_add ((actualWeighted.1.const_mul omega).add (memoryWeighted.1.const_mul (bound * omega))) actualWeighted.2.2.1,
      intervalIntegral.integral_add (actualWeighted.1.const_mul omega) (memoryWeighted.1.const_mul (bound * omega)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  have coordinateBound : size time ≤ shape time + bound * Real.exp (omega * time) *
      (omega * weighted size + bound * omega * weighted memory + weighted forcing) := by
    have comparison := intervalIntegral.integral_mono_on inside.1 (budgetIntegrable.mono_set prefixSet)
      ((kernelContinuous.continuousOn.mul upperContinuous).intervalIntegrable_of_Icc (μ := volume) inside.1) (by
        intro current member
        have rawBound := (mul_le_of_le_one_left (rawNonnegative current) epsilonOne).trans (rawMemory current (prefixSubset member))
        have inputBound : omega * (size current + epsilon * raw current) + foreign current ≤ upper current := by
          have physicalPositive := prepared.physicalForeignSourceForcing_nonneg index current
          dsimp only [upper, forcing]; nlinarith only [mul_le_mul_of_nonneg_left rawBound omegaNonnegative, physicalPositive]
        exact inputBound.trans (by
          have kernelOne : 1 ≤ kernel current := Real.one_le_exp_iff.mpr (mul_nonneg omegaNonnegative (sub_nonneg.mpr member.2))
          exact le_mul_of_one_le_left (upperNonnegative current member) kernelOne))
    rw [upperIdentity] at comparison
    have larger := mul_le_mul_of_nonneg_left comparison (zero_le_one.trans historyOne)
    have increase := mul_le_mul_of_nonneg_right historyBelow (show 0 ≤ Real.exp (omega * time) *
      (omega * weighted size + bound * omega * weighted memory + weighted forcing) by
        have memoryIntegralNonnegative := nonnegative memory (fun current member => memoryNonnegative current (prefixSubset member)); positivity)
    have actual := history time inside
    change size time ≤ shape time + historyConstant * _ at actual
    exact actual.trans ((add_le_add_left (larger.trans increase) (shape time)).trans_eq (by ring))
  have rawBound : raw time ≤ bound ^ 3 * Real.exp (omega * time) * (omega * weighted size + weighted forcing) := by
    have centerContinuous := (states prepared capPositive capState path index).2.1.mono (Icc_subset_Icc le_rfl (inside.2.trans finishBound))
    have originalContinuous : ContinuousOn (fun current => Real.exp (rate * (time - current)) *
      (omega * centered current + physical current)) (Icc 0 time) := by
      exact (show Continuous (fun current : ℝ => Real.exp (rate * (time - current))) by fun_prop).continuousOn.mul
        ((continuousOn_const.mul centerContinuous).add (physicalContinuous.mono prefixSubset))
    have comparison := intervalIntegral.integral_mono_on inside.1 (originalContinuous.intervalIntegrable_of_Icc (μ := volume) inside.1)
      (((kernelContinuous.continuousOn.mul ((continuousOn_const.mul (sizeContinuous.mono prefixSubset)).add
        (forcingContinuous.mono prefixSubset))).intervalIntegrable_of_Icc (μ := volume) inside.1).const_mul bound) (by
        intro current member
        have inputBound : omega * centered current + physical current ≤ bound * (omega * size current + forcing current) := by
          have main := mul_le_mul_of_nonneg_left (centeredBound current (prefixSubset member)) omegaNonnegative
          have source : physical current ≤ bound * forcing current :=
            (le_add_of_nonneg_left (foreignNonnegative current)).trans
              (le_mul_of_one_le_left (forcingNonnegative current) boundOne)
          exact (add_le_add main source).trans_eq (by ring)
        have kernelBound := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right rateOmega (sub_nonneg.mpr member.2))
        have centerNonnegative : 0 ≤ centered current := by
          dsimp only [centered, CascadeSourcePreparedPair.rawSourceCenteredState]; positivity
        exact (mul_le_mul kernelBound inputBound
          (add_nonneg (mul_nonneg omegaNonnegative centerNonnegative) (prepared.physicalForeignSourceForcing_nonneg index current))
          (Real.exp_pos _).le).trans_eq (by dsimp only [kernel, size]; ring))
    rw [intervalIntegral.integral_const_mul, extract] at comparison
    have integrals : weighted (fun current => omega * size current + forcing current) = omega * weighted size + weighted forcing := by
      dsimp only [weighted]; simp_rw [mul_add, mul_left_comm (Real.exp (-omega * _)) omega]
      rw [intervalIntegral.integral_add (actualWeighted.1.const_mul omega) actualWeighted.2.2.1, intervalIntegral.integral_const_mul]
    rw [integrals] at comparison
    have preliminary := (rawMemory time inside).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left comparison (zero_le_one.trans memoryOne)) boundNonnegative)
    have coefficient : bound * memoryConstant * bound ≤ bound ^ 3 := by
      nlinarith only [mul_le_mul_of_nonneg_left memoryBelow (sq_nonneg bound)]
    have increased := mul_le_mul_of_nonneg_right coefficient (show 0 ≤ Real.exp (omega * time) *
      (omega * weighted size + weighted forcing) by positivity)
    exact preliminary.trans (by convert increased using 1 <;> dsimp only [memory] <;> ring)
  have combined : size time + raw time ≤ shape time + joint * Real.exp (omega * time) *
      (omega * weighted size + weighted forcing) := by
    have scaled := mul_le_mul_of_nonneg_left memoryIntegralBound (show 0 ≤ bound ^ 2 * Real.exp (omega * time) by positivity)
    have extra := add_nonneg (mul_nonneg (show 0 ≤ bound + 2 * bound ^ 4 + bound ^ 3 by positivity) sourceIntegralNonnegative)
      (mul_nonneg (show 0 ≤ bound + 3 * bound ^ 3 by positivity) (mul_nonneg omegaNonnegative sizeIntegralNonnegative))
    dsimp only [joint]
    nlinarith only [coordinateBound, rawBound, scaled, mul_nonneg (Real.exp_pos (omega * time)).le extra]
  have finalInterior : omega * weighted size + weighted forcing ≤ (bound + 1) * (omega * weighted shape + weighted forcing) := by
    nlinarith only [sizeIntegralBound, mul_nonneg omegaNonnegative shapeIntegralNonnegative]
  have endpoint := combined.trans (add_le_add_left (mul_le_mul_of_nonneg_left finalInterior
    (show 0 ≤ joint * Real.exp (omega * time) by positivity)) (shape time))
  have lambdaI := sourceI.mono_set prefixSet
  have twoRate := General.two_rate_exponential_response_le inside.1 omegaNonnegative lambdaGap magnitudeNonnegative
    actualWeighted.2.1 actualWeighted.2.2.1 lambdaI (fun current _ => forcingNonnegative current)
    (fun current member => profile current (prefixSubset member))
  have gapRatio : omega / (growth - omega) ≤ 1 := by
    have rootTwo : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    apply (div_le_one (sub_pos.mpr lambdaGap)).mpr
    dsimp only [growth]; nlinarith only [mul_nonneg omegaNonnegative (sub_nonneg.mpr rootTwo)]
  have sourcePrefixBound : (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * forcing current) ≤ action * Real.exp (-growth * origin) := by
    apply le_trans _ sourceBudget
    exact intervalIntegral.integral_mono_interval le_rfl inside.1 inside.2
      (ae_of_all _ (fun current => mul_nonneg (Real.exp_pos _).le (forcingNonnegative current))) sourceI
  have sourceScaled := mul_le_mul_of_nonneg_left sourcePrefixBound (Real.exp_pos (growth * time)).le
  have exponential : Real.exp (growth * time) * Real.exp (-growth * origin) = Real.exp (growth * (time - origin)) := by
    rw [← Real.exp_add]; congr 1; ring
  have response : Real.exp (omega * time) * (omega * weighted shape + weighted forcing) ≤
      (magnitude + action) * Real.exp (growth * (time - origin)) := by
    have ratioScaled := mul_le_mul_of_nonneg_right gapRatio
      (mul_nonneg magnitudeNonnegative (Real.exp_pos (growth * (time - origin))).le)
    rw [mul_left_comm (Real.exp (growth * time)) action, exponential] at sourceScaled
    nlinarith only [twoRate, ratioScaled, sourceScaled]
  have final : size time + raw time ≤ shape time + joint * (bound + 1) *
      ((magnitude + action) * Real.exp (growth * (time - origin))) := by
    apply endpoint.trans
    calc
      _ = shape time + joint * (bound + 1) *
          (Real.exp (omega * time) * (omega * weighted shape + weighted forcing)) := by ring
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left response (by positivity)) _
  have profileAt := profile time inside
  dsimp only [constant]
  nlinarith only [final, profileAt, mul_nonneg actionNonnegative (Real.exp_pos (growth * (time - origin))).le]

end EulerNonuniqueness.Paper

