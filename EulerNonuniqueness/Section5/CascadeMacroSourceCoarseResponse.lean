import EulerNonuniqueness.Section5.CascadeCoarseSourceResponse
import EulerNonuniqueness.Section5.CascadeFiniteCoordinateGeometry
import EulerNonuniqueness.Section5.CascadePhaseLiftCoherence

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_macro_source_coarse_response :
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
    let changed : Scales := {scales with frequency := frequency}
    let forcing := fun time => prepared.finiteCoordinateForeignForcing index time +
      prepared.physicalForeignSourceForcing index time
    ContinuousOn forcing (Icc 0 finish) ∧ IntervalIntegrable forcing volume 0 finish ∧
    ∀ time ∈ Icc 0 finish,
      IntervalIntegrable (fun current => Real.exp (constant * changed.omega (index.val + 1) * (time - current)) *
        forcing current) volume 0 time ∧
      prepared.macroSourceState time index ≤ constant * ∫ current in (0 : ℝ)..time,
        Real.exp (constant * changed.omega (index.val + 1) * (time - current)) * forcing current := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, responses⟩ :=
    exists_uniform_actual_coarse_source_response
  obtain ⟨geometryRadius, geometryPositive, _, geometryConstant, geometryOne, geometries⟩ :=
    exists_uniform_actual_finite_coordinate_geometry_of_normalForm graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨responseRadius, responsePositive, responseQuarter, responseConstant, responseOne, rootMin, rootEight, responseParameters⟩ :=
    responses factorPositive factorSmall
  let radius := min responseRadius geometryRadius
  let constant := geometryConstant * responseConstant
  have geometryNonnegative : 0 ≤ geometryConstant := zero_le_one.trans geometryOne
  have responseNonnegative : 0 ≤ responseConstant := zero_le_one.trans responseOne
  have responseBelow : responseConstant ≤ constant :=
    le_mul_of_one_le_left responseNonnegative geometryOne
  have constantOne : 1 ≤ constant := responseOne.trans responseBelow
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  refine ⟨radius, lt_min responsePositive geometryPositive, (min_le_left _ _).trans responseQuarter,
    constant, constantOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne orbit sectionTime
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [responseParameters scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold
      referenceConstant boundaryConstant thresholdBound referenceNonnegative boundaryOne orbit sectionTime,
    geometries scales amplitudePositive ratioBound alphaPositive (zero_lt_one.trans_le rootOne)
      (zero_le_one.trans boundaryOne) factorPositive (factorSmall.trans (by norm_num)) thresholdSmall referenceNonnegative,
    scales.eventually_cascade_phase_lift_coherence ratioBound alphaPositive referenceNonnegative,
    eventually_ge_atTop (1 : ℝ)] with frequency responseEstimate geometryEstimate coherence frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound small
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let forcing := fun time => prepared.finiteCoordinateForeignForcing index time +
    prepared.physicalForeignSourceForcing index time
  let omega := changed.omega (index.val + 1)
  obtain ⟨lift, liftProperties, polar, _, _, forcingContinuous, physicalContinuous, _, _, _, _, _, responseBound⟩ :=
    responseEstimate count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound
      (fun time inside => (small time inside).trans (min_le_left _ _))
  obtain ⟨geometryLift, geometryProperties, geometryPolar, _, _, _, geometryBounds⟩ :=
    geometryEstimate prepared path index nonterminal finish finishNonnegative finishBound
      (fun time inside => (small time inside).trans (min_le_right _ _))
  have sizeEquality := (coherence prepared path index finish finishNonnegative finishBound
    (fun time inside => (small time inside).trans ((min_le_left _ _).trans responseQuarter))
    geometryLift lift (fun side => (geometryProperties side).1.continuousOn)
    (fun side => (liftProperties side).1.continuousOn)
    (fun side => (geometryProperties side).2.trans (liftProperties side).2.symm)
    geometryPolar polar).2.2 graph coordinate
  have macroBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.macroSourceState time index ≤ geometryConstant *
        (prepared.finiteCoordinateSize graph coordinate lift index time + raw time) := by
    have actual := (geometryBounds time inside).2
    rw [sizeEquality inside] at actual
    exact actual
  have forcingC0 : ContinuousOn forcing (Icc 0 finish) := forcingContinuous.add physicalContinuous
  have forcingNonnegative (time : ℝ) : 0 ≤ forcing time := by
    have locationPositive := changed.location_pos (index.val + 1)
    have first : 0 ≤ prepared.finiteCoordinateForeignForcing index time := by
      dsimp only [CascadeSourcePreparedPair.finiteCoordinateForeignForcing]
      positivity
    exact add_nonneg first (prepared.physicalForeignSourceForcing_nonneg index time)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaNonnegative : 0 ≤ omega := (changed.omega_pos frequencyPositive ratioPositive _).le
  refine ⟨forcingC0, forcingC0.intervalIntegrable_of_Icc (μ := volume) finishNonnegative, ?_⟩
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have kernelContinuous (coefficient : ℝ) :
      Continuous (fun current : ℝ => Real.exp (coefficient * omega * (time - current))) := by fun_prop
  have integrable (coefficient : ℝ) : IntervalIntegrable
      (fun current => Real.exp (coefficient * omega * (time - current)) * forcing current) volume 0 time :=
    ((kernelContinuous coefficient).continuousOn.mul (forcingC0.mono subset)).intervalIntegrable_of_Icc inside.1
  have comparison := intervalIntegral.integral_mono_on (μ := volume) inside.1
    (integrable responseConstant) (integrable constant) (by
      intro current member
      have rates := mul_le_mul_of_nonneg_right responseBelow omegaNonnegative
      have exponential := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right rates (sub_nonneg.mpr member.2))
      exact mul_le_mul_of_nonneg_right exponential (forcingNonnegative current))
  refine ⟨integrable constant, ?_⟩
  have actual := (macroBound time inside).trans
    (mul_le_mul_of_nonneg_left (responseBound time inside) geometryNonnegative)
  calc
    prepared.macroSourceState time index ≤ geometryConstant *
        (responseConstant * ∫ current in (0 : ℝ)..time,
          Real.exp (responseConstant * omega * (time - current)) * forcing current) := actual
    _ = constant * ∫ current in (0 : ℝ)..time,
        Real.exp (responseConstant * omega * (time - current)) * forcing current := by dsimp only [constant]; ring
    _ ≤ constant * ∫ current in (0 : ℝ)..time,
        Real.exp (constant * omega * (time - current)) * forcing current :=
      mul_le_mul_of_nonneg_left comparison constantNonnegative

end EulerNonuniqueness.Paper

