import EulerNonuniqueness.Section5.CascadeExponentialIntegratedNonlinearCoefficient
import EulerNonuniqueness.Section5.Delay
import EulerNonuniqueness.General.ExponentialAccumulatedCost

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem action_rate_gain_le {omega growth : ℝ}
    (omegaPositive : 0 < omega) (growthLower : omega ≤ growth) :
    (2 * omega / growth ^ 2 + 1 / growth) * omega ≤ 3 := by
  have growthPositive : 0 < growth := omegaPositive.trans_le growthLower
  have quotientNonnegative : 0 ≤ omega / growth := div_nonneg omegaPositive.le growthPositive.le
  have quotientBound : omega / growth ≤ 1 := (div_le_one growthPositive).mpr growthLower
  calc
    _ = 2 * (omega / growth) ^ 2 + omega / growth := by field_simp; ring
    _ ≤ 3 := by nlinarith only [quotientNonnegative, quotientBound]

theorem exists_uniform_actual_small_integrated_nonlinear_coefficient :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ stableConstant ≥ (1 : ℝ), ∃ dilationConstant ≥ (0 : ℝ),
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∀ magnitude : ℝ, 0 ≤ magnitude → ∀ actionTolerance : ℝ, 0 < actionTolerance →
      let endpointSize := actionTolerance / (12 * (magnitude + 1))
      0 < endpointSize ∧
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
      ∀ {scaleRoot boundaryConstant threshold referenceConstant tolerance : ℝ},
      1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ thresholdMax → 0 ≤ referenceConstant → 0 < tolerance →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let relative := fun time => referenceStraightenedShape first graph coordinate index time -
        referenceStraightenedShape second graph coordinate index time
      let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time index
      let remainder := relativeStraightenedSaddleStrainRemainder changed
        (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index
      let omega := changed.omega (index.val + 1)
      let growth := 2 * Real.sqrt 2 * omega
      let length := changed.length (index.val + 1)
      let centerRadius := factor / 39321600 * changed.location (index.val + 1)
      let patchRadius := factor / 39321600 * length
      let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
      let center := fun time => prepared.rawSourceCenteredState time index
      let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
      let moment := fun time => ‖relativeNormalizedFirstMoment changed first second index time‖
      let shape := fun time => |(relative time).1| + |(relative time).2|
      let dilation := fun time => |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2
      let indexedReferenceSize := chartConstant * referenceConstant *
        ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
      let coefficient := fun time => indexedReferenceSize + dilation time + |(relative time).2|
      let graded := fun time => coefficient time * shape time + indexedReferenceSize * dilation time
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
      let dilationMajorant := fun time => tolerance * moment time +
        (tolerance + dilationConstant * changed.strain + dilationConstant * omega * epsilon) * center time +
        dilationConstant * omega * epsilon * raw time + dilationConstant * difference time +
        dilationConstant * epsilon * ∑ patch : Fin 4, foreign patch time
      let forcing := fun time => |(leading time).2| + tolerance * (moment time + center time + shape time) +
        stableConstant * omega * epsilon * (center time + raw time) +
        stableConstant * epsilon * ∑ patch : Fin 4, foreign patch time +
        stableConstant * (length / centerRadius) * (changed.strain * center time + difference time) +
        stableConstant * indexedReferenceSize * ‖leading time‖
      let upper := fun time => stableConstant * omega * graded time + tolerance * (moment time + center time + shape time) +
        stableConstant * omega * epsilon * (center time + raw time) +
        stableConstant * epsilon * ∑ patch : Fin 4, foreign patch time +
        stableConstant * (length / centerRadius) * (changed.strain * center time + difference time) +
        stableConstant * indexedReferenceSize * ‖leading time‖
      ((ContinuousOn coefficient (Icc 0 finish) ∧ ContinuousOn dilationMajorant (Icc 0 finish) ∧
      ContinuousOn forcing (Icc 0 finish) ∧
      IntervalIntegrable coefficient volume 0 finish ∧
      IntervalIntegrable (fun time => (finish - time) * dilationMajorant time) volume 0 finish ∧
      IntervalIntegrable forcing volume 0 finish ∧
      (omega * (∫ time in (0 : ℝ)..finish, coefficient time) ≤
        2 * omega * indexedReferenceSize * finish +
          2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time) +
          ∫ time in (0 : ℝ)..finish, forcing time) ∧
      0 < growth ∧ ContinuousOn relative (Icc 0 finish) ∧ ContinuousOn leading (Icc 0 finish) ∧
      ContinuousOn remainder (Icc 0 finish) ∧
      IntervalIntegrable (fun time => ‖remainder time‖) volume 0 finish ∧
      IntervalIntegrable upper volume 0 finish ∧
      (∀ time ∈ Ioo 0 finish, ‖remainder time‖ ≤ upper time) ∧
      (∀ time ∈ Icc 0 finish,
        (∫ current in (0 : ℝ)..time, ‖remainder current‖) ≤ ∫ current in (0 : ℝ)..time, upper current ∧
        Real.exp (-growth * time) * (relative time).1 =
          (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current).1) +
            ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (remainder current).1 ∧
        (relative time).2 = ∫ current in (0 : ℝ)..time,
          Real.exp (-growth * (time - current)) * (leading current + remainder current).2 ∧
        |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
          Real.exp (-growth * (time - current)) * (|(leading current).2| + upper current)) ∧
      growth * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(relative time).2|) ≤
        (1 / 2 : ℝ) * ((∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(leading time).2|) +
          ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * upper time)) ∧
      ∀ rate : ℝ, 0 < rate → ∀ origin bound : ℝ, 0 ≤ bound →
        (∀ time ∈ Icc 0 finish, dilationMajorant time ≤ bound * Real.exp (rate * (time - origin))) →
        (∀ time ∈ Icc 0 finish, forcing time ≤ bound * Real.exp (rate * (time - origin))) →
        omega * (∫ time in (0 : ℝ)..finish, coefficient time) ≤
          2 * omega * indexedReferenceSize * finish +
            (2 * omega / rate ^ 2 + 1 / rate) * bound * Real.exp (rate * (finish - origin))) ∧
      ∀ origin : ℝ,
        (∀ time ∈ Icc 0 finish, dilationMajorant time ≤ magnitude * omega * changed.seed (index.val + 1) *
          Real.exp (growth * (time - origin))) →
        (∀ time ∈ Icc 0 finish, forcing time ≤ magnitude * omega * changed.seed (index.val + 1) *
          Real.exp (growth * (time - origin))) →
        changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ≤ endpointSize →
        (2 * omega * indexedReferenceSize * finish +
          2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationMajorant time) +
          (∫ time in (0 : ℝ)..finish, forcing time) < actionTolerance) ∧
        omega * (∫ time in (0 : ℝ)..finish, coefficient time) < actionTolerance := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, capPositive, factory⟩ := exists_uniform_actual_exponential_integrated_nonlinear_coefficient
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, radius, radiusPositive, radiusQuarter, actual⟩ :=
    factory factorPositive factorSmall
  refine ⟨stableConstant, stableOne, dilationConstant, dilationNonnegative, radius, radiusPositive, radiusQuarter, ?_⟩
  intro magnitude magnitudeNonnegative actionTolerance actionTolerancePositive
  dsimp only
  refine ⟨by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant tolerance
    rootOne boundaryOne thresholdBound referenceNonnegative tolerancePositive
  have referenceCoefficientNonnegative : 0 ≤ 2 * chartConstant * referenceConstant :=
    mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans chartOne)) referenceNonnegative
  filter_upwards [actual scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdBound referenceNonnegative tolerancePositive,
    scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive referenceCoefficientNonnegative
      (show 0 < actionTolerance / 8 by positivity),
    eventually_ge_atTop (1 : ℝ)] with frequency estimate referenceEstimate frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  have data := estimate count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  dsimp only at data
  refine ⟨data, ?_⟩
  intro origin dilationProfile forcingProfile endpointBound
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let seed := changed.seed (index.val + 1)
  let referenceSize := chartConstant * referenceConstant *
    ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  let endpointSize := actionTolerance / (12 * (magnitude + 1))
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaOne : 1 ≤ omega := frequencyOne.trans
    (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have growthPositive : 0 < growth := data.1.2.2.2.2.2.2.2.1
  have growthLower : omega ≤ growth := by
    have rootBound : 1 ≤ 2 * Real.sqrt 2 := by
      nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right rootBound omegaPositive.le
  have referenceNonnegative : 0 ≤ 2 * omega * referenceSize := by
    convert (referenceEstimate (index.val + 1)).1 using 1
    dsimp only [changed, omega, referenceSize]
    ring
  have referenceSmall : 2 * omega * referenceSize < actionTolerance / 8 := by
    convert (referenceEstimate (index.val + 1)).2 using 1
    dsimp only [changed, omega, referenceSize]
    ring
  have finishOne : finish ≤ 1 := finishBound.trans path.stopBound
  have referenceActionSmall : 2 * omega * referenceSize * finish < actionTolerance / 8 :=
    (mul_le_of_le_one_right referenceNonnegative finishOne).trans_lt referenceSmall
  have costEstimate := General.accumulated_cost_le_of_exponential_majorants (referenceSize := referenceSize)
    finishNonnegative growthPositive (show 0 ≤ magnitude * omega * seed by positivity) omegaPositive.le
    data.1.2.1 data.1.2.2.1 dilationProfile forcingProfile
  have gainBound := action_rate_gain_le omegaPositive growthLower
  have profileBound : (2 * omega / growth ^ 2 + 1 / growth) * (magnitude * omega * seed) *
      Real.exp (growth * (finish - origin)) ≤ 3 * magnitude * endpointSize := by
    calc
      _ = ((2 * omega / growth ^ 2 + 1 / growth) * omega) *
          (magnitude * (seed * Real.exp (growth * (finish - origin)))) := by ring
      _ ≤ 3 * (magnitude * (seed * Real.exp (growth * (finish - origin)))) :=
        mul_le_mul_of_nonneg_right gainBound (by positivity)
      _ ≤ 3 * (magnitude * endpointSize) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left endpointBound magnitudeNonnegative) (by norm_num)
      _ = _ := by ring
  have endpointPositive : 0 < endpointSize := by dsimp only [endpointSize]; positivity
  have profileCostBound : 3 * magnitude * endpointSize ≤ actionTolerance / 4 := by
    have comparison := mul_le_mul_of_nonneg_right
      (show 3 * magnitude ≤ 3 * (magnitude + 1) by linarith) endpointPositive.le
    have identity : 3 * (magnitude + 1) * endpointSize = actionTolerance / 4 := by
      dsimp only [endpointSize]
      field_simp
      ring
    exact comparison.trans_eq identity
  have finalBound := costEstimate.trans (add_le_add_left profileBound (2 * omega * referenceSize * finish))
  have rightSmall : 2 * omega * referenceSize * finish + 3 * magnitude * endpointSize < actionTolerance := by
    linarith only [referenceActionSmall, profileCostBound, actionTolerancePositive]
  have costSmall := finalBound.trans_lt rightSmall
  exact ⟨costSmall, data.1.2.2.2.2.2.2.1.trans_lt costSmall⟩

end EulerNonuniqueness.Paper

