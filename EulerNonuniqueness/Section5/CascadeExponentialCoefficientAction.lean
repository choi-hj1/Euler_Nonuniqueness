import EulerNonuniqueness.Section5.CascadeFirstMomentLocalForeignHistory
import EulerNonuniqueness.Section5.CascadeDilationLocalForeignHistory
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics
import EulerNonuniqueness.General.ExponentialNestedHistoryAction

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_exponential_coefficient_action :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ momentConstant ≥ (0 : ℝ), ∃ dilationConstant ≥ (0 : ℝ),
    ∀ graph coordinate : ℝ → ℝ, ∀ chartConstant : ℝ, 0 ≤ chartConstant →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {scaleRoot boundaryConstant threshold referenceConstant : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let omega := changed.omega (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let moment := fun time => ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖
    let dilation := fun time => |(diagonalDifference first.patchMotion time index -
      diagonalDifference second.patchMotion time index) / changed.length (index.val + 1) ^ 2|
    let stable := fun time => (referenceStraightenedShape first.patchMotion graph coordinate index time -
      referenceStraightenedShape second.patchMotion graph coordinate index time).2
    let difference := fun time => ∑' power : ℕ,
      ‖quadrupoleExteriorCoefficient changed first.patchMotion index time
          (factor / 39321600 * changed.location (index.val + 1)) power -
        quadrupoleExteriorCoefficient changed second.patchMotion index time
          (factor / 39321600 * changed.location (index.val + 1)) power‖
    let foreign := fun (radius : ℝ) (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖
    let momentForcing := fun time => momentConstant *
      (changed.strain * prepared.rawSourceCenteredState time index + difference time +
        epsilon * (changed.strain * (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
          ∑ patch : Fin 4, foreign (factor / 39321600 * changed.location (index.val + 1)) patch time))
    let dilationForcing := fun time =>
      (1 + dilationConstant * changed.strain + dilationConstant * omega * epsilon) * prepared.rawSourceCenteredState time index +
        dilationConstant * omega * epsilon * (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
        dilationConstant * difference time + dilationConstant * epsilon *
          ∑ patch : Fin 4, foreign (factor / 39321600 * changed.length (index.val + 1)) patch time
    let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
    ∀ forcingConstant rate origin : ℝ, 0 ≤ forcingConstant → 0 < rate →
    ContinuousOn stable (Icc 0 finish) →
    (∀ time ∈ Icc 0 finish, momentForcing time ≤ forcingConstant * Real.exp (rate * (time - origin))) →
    (∀ time ∈ Icc 0 finish, dilationForcing time ≤ forcingConstant * Real.exp (rate * (time - origin))) →
    (∀ time ∈ Icc 0 finish,
      moment time ≤ forcingConstant / rate * Real.exp (rate * (time - origin)) ∧
      dilation time ≤ forcingConstant * (1 / rate + 1 / rate ^ 2) * Real.exp (rate * (time - origin))) ∧
    ContinuousOn (fun time => referenceSize + dilation time + |stable time|) (Icc 0 finish) ∧
    IntervalIntegrable (fun time => referenceSize + dilation time + |stable time|) volume 0 finish ∧
    IntervalIntegrable (fun time => |stable time|) volume 0 finish ∧
    omega * (∫ time in (0 : ℝ)..finish, referenceSize + dilation time + |stable time|) ≤
      omega * referenceSize * finish + omega * (∫ time in (0 : ℝ)..finish, |stable time|) +
        omega * forcingConstant * (1 / rate ^ 2 + 1 / rate ^ 3) * Real.exp (rate * (finish - origin)) := by
  obtain ⟨momentCap, momentPositive, momentFactory⟩ := exists_uniform_actual_firstMoment_local_foreign_history
  obtain ⟨dilationCap, dilationPositive, dilationFactory⟩ := exists_uniform_actual_prehit_dilation_local_foreign_history
  obtain ⟨stateCap, statePositive, stateFactory⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min momentCap (min dilationCap stateCap)
  have capPositive : 0 < rawCap := lt_min momentPositive (lt_min dilationPositive statePositive)
  have momentCapBound : rawCap ≤ momentCap := min_le_left _ _
  have dilationCapBound : rawCap ≤ dilationCap := (min_le_right _ _).trans (min_le_left _ _)
  have stateCapBound : rawCap ≤ stateCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨momentConstant, momentNonnegative, moments⟩ := momentFactory factorPositive (factorSmall.trans (by norm_num))
  obtain ⟨dilationConstant, dilationNonnegative, dilations⟩ := dilationFactory factorPositive factorSmall
  refine ⟨momentConstant, momentNonnegative, dilationConstant, dilationNonnegative, ?_⟩
  intro graph coordinate chartConstant _chartNonnegative scales amplitudePositive ratioBound alphaPositive orbit sectionTime
    scaleRoot boundaryConstant threshold referenceConstant rootOne boundaryOne thresholdSmall referenceNonnegative
  filter_upwards [moments scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne,
    dilations scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with frequency momentEstimate dilationEstimate frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let moment := fun time => ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖
  let dilation := fun time => |(diagonalDifference first.patchMotion time index -
      diagonalDifference second.patchMotion time index) / changed.length (index.val + 1) ^ 2|
  let stable := fun time => (referenceStraightenedShape first.patchMotion graph coordinate index time -
      referenceStraightenedShape second.patchMotion graph coordinate index time).2
  let difference := fun time => ∑' power : ℕ,
      ‖quadrupoleExteriorCoefficient changed first.patchMotion index time
          (factor / 39321600 * changed.location (index.val + 1)) power -
        quadrupoleExteriorCoefficient changed second.patchMotion index time
          (factor / 39321600 * changed.location (index.val + 1)) power‖
  let foreign := fun (radius : ℝ) (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖
  let momentForcing := fun time => momentConstant *
      (changed.strain * prepared.rawSourceCenteredState time index + difference time +
        epsilon * (changed.strain * (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
          ∑ patch : Fin 4, foreign (factor / 39321600 * changed.location (index.val + 1)) patch time))
  let dilationForcing := fun time =>
      (1 + dilationConstant * changed.strain + dilationConstant * omega * epsilon) * prepared.rawSourceCenteredState time index +
        dilationConstant * omega * epsilon * (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
        dilationConstant * difference time + dilationConstant * epsilon *
          ∑ patch : Fin 4, foreign (factor / 39321600 * changed.length (index.val + 1)) patch time
  let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  intro forcingConstant rate origin forcingNonnegative ratePositive stableContinuous momentBound dilationBound
  have centerInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have firstInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).trajectory.movingFamily = prepared.trajectory.movingFamily := by rfl
  have secondInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).referenceWitness.trajectory.movingFamily =
        prepared.referenceWitness.trajectory.movingFamily := by rfl
  have momentData := momentEstimate count phase dipoleAngle (prepared.enlargeCap momentCapBound) path
    index nonterminal finish finishNonnegative finishBound radialSmall
  dsimp only at momentData
  simp only [centerInvariant, rawInvariant, firstInvariant, secondInvariant] at momentData
  have dilationData := dilationEstimate count phase dipoleAngle (prepared.enlargeCap dilationCapBound) path
    index nonterminal finish finishNonnegative finishBound radialSmall
  dsimp only at dilationData
  simp only [centerInvariant, rawInvariant, firstInvariant, secondInvariant, one_mul] at dilationData
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have stateData := stateFactory prepared capPositive stateCapBound path index
  have centerIntegrable := (stateData.2.1.mono subset).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have rawContinuous : ContinuousOn (fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch)
      (Icc 0 finish) :=
    continuousOn_finset_sum Finset.univ (fun patch _ => (stateData.1 patch).mono subset)
  have rawIntegrable := rawContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have foreignIntegrable (patch : Fin 4) : IntervalIntegrable
      (foreign (factor / 39321600 * changed.location (index.val + 1)) patch) volume 0 finish := momentData.2.1 patch
  have foreignSumIntegrable : IntervalIntegrable
      (fun time => ∑ patch : Fin 4, foreign (factor / 39321600 * changed.location (index.val + 1)) patch time)
      volume 0 finish := by
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ
      (f := foreign (factor / 39321600 * changed.location (index.val + 1))) (fun patch _ => foreignIntegrable patch)
  have momentForcingIntegrable : IntervalIntegrable momentForcing volume 0 finish :=
    (((centerIntegrable.const_mul changed.strain).add momentData.1).add
      (((rawIntegrable.const_mul changed.strain).add foreignSumIntegrable).const_mul epsilon)).const_mul momentConstant
  have momentHistory : ∀ time ∈ Icc 0 finish, moment time ≤ ∫ current in (0 : ℝ)..time, momentForcing current := by
    intro time inside
    exact (momentData.2.2 time inside).trans_eq (intervalIntegral.integral_const_mul ..).symm
  have dilationForcingIntegrable : IntervalIntegrable
      (fun time => moment time + dilationForcing time) volume 0 finish := by
    convert dilationData.2.2.2.2.2.1 using 1
    ext time
    dsimp only [moment, dilationForcing, omega, changed, first, second, epsilon, difference, foreign]
    ring
  have dilationHistory : ∀ time ∈ Icc 0 finish,
      dilation time ≤ ∫ current in (0 : ℝ)..time, moment current + dilationForcing current := by
    intro time inside
    refine (dilationData.2.2.2.2.2.2 time inside).trans_eq ?_
    apply intervalIntegral.integral_congr
    intro current _
    dsimp only [moment, dilationForcing, omega, changed, first, second, epsilon, difference, foreign]
    ring
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaNonnegative : 0 ≤ omega := (changed.omega_pos frequencyPositive ratioPositive _).le
  have momentVectorContinuous : ContinuousOn
      (relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index) (Icc 0 finish) := by
    intro time inside
    have actual := path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index (subset inside)
    simpa only [first, second, prepared.referenceIdentity] using actual.continuousAt.continuousWithinAt
  have momentContinuous : ContinuousOn moment (Icc 0 finish) := momentVectorContinuous.norm
  exact General.exponential_nested_history_action_on_Icc finishNonnegative ratePositive forcingNonnegative omegaNonnegative
    momentContinuous dilationData.1.abs stableContinuous momentForcingIntegrable dilationForcingIntegrable
    momentHistory dilationHistory momentBound dilationBound

end EulerNonuniqueness.Paper

