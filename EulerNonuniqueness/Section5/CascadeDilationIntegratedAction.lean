import EulerNonuniqueness.Section5.CascadeDilationLocalForeignHistory
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadeForeignCoefficientSeriesContinuity
import EulerNonuniqueness.General.IntegratedPrimitiveAction

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_dilation_integrated_action :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 → ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {scaleRoot boundaryConstant threshold referenceConstant tolerance : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 0 < tolerance →
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
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let centerRadius := factor / 39321600 * changed.location (index.val + 1)
    let patchRadius := factor / 39321600 * changed.length (index.val + 1)
    let dilation := fun time => |diagonalDifference first.patchMotion time index - diagonalDifference second.patchMotion time index| /
      changed.length (index.val + 1) ^ 2
    let difference := fun time => ∑' power : ℕ,
      ‖quadrupoleExteriorCoefficient changed first.patchMotion index time centerRadius power -
        quadrupoleExteriorCoefficient changed second.patchMotion index time centerRadius power‖
    let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
    let majorant := fun time =>
      tolerance * ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ +
        (tolerance + constant * changed.strain + constant * changed.omega (index.val + 1) * epsilon) *
          prepared.rawSourceCenteredState time index +
        constant * changed.omega (index.val + 1) * epsilon * (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
        constant * difference time + constant * epsilon * ∑ patch : Fin 4, foreign patch time
    ContinuousOn dilation (Icc 0 finish) ∧ ContinuousOn majorant (Icc 0 finish) ∧
    IntervalIntegrable dilation volume 0 finish ∧
    IntervalIntegrable (fun time => (finish - time) * majorant time) volume 0 finish ∧
    changed.omega (index.val + 1) * (∫ time in (0 : ℝ)..finish, dilation time) ≤
      changed.omega (index.val + 1) * ∫ time in (0 : ℝ)..finish, (finish - time) * majorant time := by
  obtain ⟨historyCap, historyPositive, historyFactory⟩ := exists_uniform_actual_prehit_dilation_local_foreign_history
  obtain ⟨stateCap, statePositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min historyCap stateCap
  have rawPositive : 0 < rawCap := lt_min historyPositive statePositive
  have historyCapBound : rawCap ≤ historyCap := min_le_left _ _
  have stateCapBound : rawCap ≤ stateCap := min_le_right _ _
  refine ⟨rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantNonnegative, histories⟩ := historyFactory factorPositive factorSmall
  refine ⟨constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant tolerance rootOne boundaryOne thresholdSmall referenceNonnegative tolerancePositive
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [histories scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative tolerancePositive,
    scales.eventually_cascade_foreign_coefficient_series_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with frequency historyEstimate seriesEstimate lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let centerRadius := factor / 39321600 * changed.location (index.val + 1)
  let patchRadius := factor / 39321600 * changed.length (index.val + 1)
  let dilation := fun time => |diagonalDifference first.patchMotion time index - diagonalDifference second.patchMotion time index| /
    changed.length (index.val + 1) ^ 2
  let difference := fun time => ∑' power : ℕ,
    ‖quadrupoleExteriorCoefficient changed first.patchMotion index time centerRadius power -
      quadrupoleExteriorCoefficient changed second.patchMotion index time centerRadius power‖
  let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
  let majorant := fun time =>
    tolerance * ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ +
      (tolerance + constant * changed.strain + constant * changed.omega (index.val + 1) * epsilon) *
        prepared.rawSourceCenteredState time index +
      constant * changed.omega (index.val + 1) * epsilon * (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
      constant * difference time + constant * epsilon * ∑ patch : Fin 4, foreign patch time
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have lengthPositive := changed.length_pos (index.val + 1)
  have denominatorPositive : 0 < changed.length (index.val + 1) ^ 2 := sq_pos_of_pos lengthPositive
  have dilationIdentity (time : ℝ) : dilation time =
      |(diagonalDifference first.patchMotion time index - diagonalDifference second.patchMotion time index) /
        changed.length (index.val + 1) ^ 2| := by
    rw [abs_div, abs_of_pos denominatorPositive]
  have historyData := historyEstimate count phase dipoleAngle (prepared.enlargeCap historyCapBound) path index nonterminal
    finish finishNonnegative finishBound radialSmall
  dsimp only at historyData
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) :=
    historyData.1.abs.congr (fun time _ => dilationIdentity time)
  have historyBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      dilation time ≤ ∫ current in (0 : ℝ)..time, majorant current := by
    rw [dilationIdentity]
    have actual := historyData.2.2.2.2.2.2 time inside
    with_reducible_and_instances
      dsimp only [majorant, epsilon, difference, foreign, centerRadius, patchRadius, first, second,
        CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState,
        CascadeSourcePreparedPair.rawSourceShapeBudget] at actual ⊢
      exact actual
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have momentContinuous : ContinuousOn
      (fun time => relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time) (Icc 0 finish) := by
    intro time inside
    have actual := path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index (subset inside)
    simpa only [first, second, prepared.referenceIdentity] using actual.continuousAt.continuousWithinAt
  have stateData := stateContinuity prepared rawPositive stateCapBound path index
  have centerContinuous := stateData.2.1.mono subset
  have rawContinuous : ContinuousOn (fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) (Icc 0 finish) :=
    continuousOn_finset_sum Finset.univ (fun patch _ => (stateData.1 patch).mono subset)
  have locationPositive := changed.location_pos (index.val + 1)
  have scalarSmall : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorSmall]
  have centerNonnegative : 0 ≤ centerRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) locationPositive.le
  have centerSmall : centerRadius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    simpa only [centerRadius, changed, div_eq_mul_inv, one_mul, mul_comm] using
      mul_le_mul_of_nonneg_right scalarSmall locationPositive.le
  have lengthBelow : changed.length (index.val + 1) ≤ changed.location (index.val + 1) := by
    simpa only [one_mul] using (lengths (index.val + 1)).le
  have patchNonnegative : 0 ≤ patchRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) lengthPositive.le
  have patchSmall : patchRadius ≤ scales.location (index.val + 1) / (100000 * 96) :=
    (mul_le_mul_of_nonneg_left lengthBelow (div_nonneg factorPositive.le (by norm_num))).trans centerSmall
  have centerData := seriesEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index
    centerRadius centerNonnegative centerSmall
  have patchData := seriesEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index
    patchRadius patchNonnegative patchSmall
  have differenceContinuous : ContinuousOn difference (Icc 0 finish) := centerData.2.2.mono subset
  have foreignContinuous (patch : Fin 4) : ContinuousOn (foreign patch) (Icc 0 finish) :=
    ((patchData.1 patch).2).mono subset
  have foreignSumContinuous : ContinuousOn (fun time => ∑ patch : Fin 4, foreign patch time) (Icc 0 finish) :=
    continuousOn_finset_sum Finset.univ (fun patch _ => foreignContinuous patch)
  have majorantContinuous : ContinuousOn majorant (Icc 0 finish) :=
    ((((continuousOn_const.mul momentContinuous.norm).add
      (continuousOn_const.mul centerContinuous)).add
      (continuousOn_const.mul rawContinuous)).add
      (continuousOn_const.mul differenceContinuous)).add (continuousOn_const.mul foreignSumContinuous)
  have remainingContinuous : ContinuousOn (fun time => (finish - time) * majorant time) (Icc 0 finish) :=
    (continuous_const.sub continuous_id).continuousOn.mul majorantContinuous
  have comparison := intervalIntegral.integral_history_le_integral_remaining_forcing finishNonnegative
    dilationContinuous majorantContinuous historyBound
  exact ⟨dilationContinuous, majorantContinuous, dilationContinuous.intervalIntegrable_of_Icc finishNonnegative,
    remainingContinuous.intervalIntegrable_of_Icc finishNonnegative,
    mul_le_mul_of_nonneg_left comparison (changed.omega_pos frequencyPositive ratioPositive (index.val + 1)).le⟩

end EulerNonuniqueness.Paper
