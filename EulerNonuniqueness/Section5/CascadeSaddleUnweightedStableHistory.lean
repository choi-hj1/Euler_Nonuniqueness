import EulerNonuniqueness.Section5.CascadeSaddleGradedLocalForeignHistory
import EulerNonuniqueness.General.WeightedResponseIntegral

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem stable_integral_of_original_history
    {relative leading remainder : ℝ → ℝ × ℝ} {growth finish : ℝ}
    (growthPositive : 0 < growth) (finishNonnegative : 0 ≤ finish)
    (relativeContinuous : ContinuousOn relative (Icc 0 finish))
    (leadingContinuous : ContinuousOn leading (Icc 0 finish))
    (remainderContinuous : ContinuousOn remainder (Icc 0 finish))
    (identity : ∀ time ∈ Icc 0 finish, (relative time).2 =
      ∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * (leading current + remainder current).2) :
    growth * (∫ time in (0 : ℝ)..finish, |(relative time).2|) ≤
      (∫ time in (0 : ℝ)..finish, |(leading time).2|) + ∫ time in (0 : ℝ)..finish, ‖remainder time‖ := by
  let forcing := fun time => |(leading time).2| + ‖remainder time‖
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) := leadingContinuous.snd.abs.add remainderContinuous.norm
  have forcingNonnegative (time : ℝ) : 0 ≤ forcing time := add_nonneg (abs_nonneg _) (norm_nonneg _)
  let extended := fun time => forcing (projIcc 0 finish finishNonnegative time)
  have extendedContinuous : Continuous extended :=
    continuousOn_iff_continuous_restrict.mp forcingContinuous |>.comp continuous_projIcc
  have agreement (time : ℝ) (inside : time ∈ Icc 0 finish) : extended time = forcing time := by
    simp only [extended, projIcc_of_mem finishNonnegative inside]
  let kernel := fun time => ∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * forcing current
  have kernelAgreement (time : ℝ) (inside : time ∈ Icc 0 finish) :
      EulerNonuniqueness.exponentialResponse (-growth) extended time = kernel time := by
    rw [EulerNonuniqueness.exponentialResponse_eq_integral]
    apply intervalIntegral.integral_congr
    intro current member
    rw [uIcc_of_le inside.1] at member
    change Real.exp (-growth * (time - current)) * extended current = _
    rw [agreement current ⟨member.1, member.2.trans inside.2⟩]
  have responseContinuous : Continuous (EulerNonuniqueness.exponentialResponse (-growth) extended) :=
    continuous_iff_continuousAt.mpr fun time =>
      (EulerNonuniqueness.hasDerivAt_exponentialResponse extendedContinuous (-growth) time).continuousAt
  have kernelContinuous : ContinuousOn kernel (Icc 0 finish) :=
    responseContinuous.continuousOn.congr (fun time inside => (kernelAgreement time inside).symm)
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : |(relative time).2| ≤ kernel time := by
    have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have exponential : Continuous (fun current : ℝ => Real.exp (-growth * (time - current))) := by fun_prop
    have absoluteIntegrable := (exponential.continuousOn.mul
      ((leadingContinuous.add remainderContinuous).snd.abs.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    have forcingIntegrable := (exponential.continuousOn.mul (forcingContinuous.mono subset)).intervalIntegrable_of_Icc
      (μ := volume) inside.1
    rw [identity time inside]
    have absoluteBound := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun current => Real.exp (-growth * (time - current)) * (leading current + remainder current).2) inside.1
    have comparison := intervalIntegral.integral_mono_on inside.1 absoluteIntegrable forcingIntegrable (by
      intro current member
      have projection : |(remainder current).2| ≤ ‖remainder current‖ := by
        simpa only [Real.norm_eq_abs] using norm_snd_le (remainder current)
      have sumBound : |(leading current + remainder current).2| ≤ forcing current :=
        (abs_add _ _).trans (add_le_add_left projection _)
      exact mul_le_mul_of_nonneg_left sumBound (Real.exp_pos _).le)
    have normalizedBound :
        |∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * (leading current + remainder current).2| ≤
          ∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * |(leading current + remainder current).2| := by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using absoluteBound
    exact normalizedBound.trans comparison
  have comparison := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative
    (relativeContinuous.snd.abs.intervalIntegrable_of_Icc finishNonnegative)
    (kernelContinuous.intervalIntegrable_of_Icc finishNonnegative) pointwise
  have convolution := EulerNonuniqueness.weighted_exponential_convolution_integral_le
    (rate := -growth) (weight := 0) forcingContinuous (by linarith only [growthPositive]) finishNonnegative
    (fun time _ => forcingNonnegative time)
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, zero_sub, neg_neg] at convolution
  have normalized := (le_div_iff₀ growthPositive).mp (comparison.trans convolution)
  rw [intervalIntegral.integral_add
    (leadingContinuous.snd.abs.intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    (remainderContinuous.norm.intervalIntegrable_of_Icc (μ := volume) finishNonnegative)] at normalized
  simpa only [mul_comm] using normalized

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_cascade_saddle_unweighted_stable_history :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 → ∃ constant ≥ (1 : ℝ),
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
      let graded := fun time => (indexedReferenceSize + dilation time + |(relative time).2|) * shape time +
        indexedReferenceSize * dilation time
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
      let upper := fun time => constant * omega * graded time + tolerance * (moment time + center time + shape time) +
        constant * omega * epsilon * (center time + raw time) +
        constant * epsilon * ∑ patch : Fin 4, foreign patch time +
        constant * (length / centerRadius) * (changed.strain * center time + difference time) +
        constant * indexedReferenceSize * ‖leading time‖
      0 < growth ∧ ContinuousOn relative (Icc 0 finish) ∧ ContinuousOn leading (Icc 0 finish) ∧
      IntervalIntegrable (fun time => |(relative time).2|) volume 0 finish ∧
      IntervalIntegrable (fun time => |(leading time).2|) volume 0 finish ∧
      IntervalIntegrable upper volume 0 finish ∧
      growth * (∫ time in (0 : ℝ)..finish, |(relative time).2|) ≤
        (∫ time in (0 : ℝ)..finish, |(leading time).2|) + ∫ time in (0 : ℝ)..finish, upper time := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    radius, radiusPositive, radiusQuarter, compatible, rawCap, rawPositive, factories⟩ :=
    exists_uniform_actual_cascade_saddle_graded_local_foreign_history
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    radius, radiusPositive, radiusQuarter, compatible, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantOne, factory⟩ := factories factorPositive factorSmall
  refine ⟨constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant tolerance
    rootOne boundaryOne thresholdBound referenceNonnegative tolerancePositive
  filter_upwards [factory scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdBound
    referenceNonnegative tolerancePositive] with frequency histories
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  obtain ⟨growthPositive, relativeContinuous, leadingContinuous, remainderContinuous, _, _, upperIntegrable, _, _, histories, _⟩ :=
    histories count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall small
  dsimp only at growthPositive relativeContinuous leadingContinuous remainderContinuous upperIntegrable histories ⊢
  refine ⟨growthPositive, relativeContinuous, leadingContinuous,
    relativeContinuous.snd.abs.intervalIntegrable_of_Icc finishNonnegative,
    leadingContinuous.snd.abs.intervalIntegrable_of_Icc finishNonnegative, upperIntegrable, ?_⟩
  have stable := stable_integral_of_original_history growthPositive finishNonnegative relativeContinuous leadingContinuous
    remainderContinuous (fun time inside => (histories time inside).2.2.1)
  exact stable.trans (add_le_add_left (histories finish ⟨finishNonnegative, le_rfl⟩).1 _)

end EulerNonuniqueness.Paper
