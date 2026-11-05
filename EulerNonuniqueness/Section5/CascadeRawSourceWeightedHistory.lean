import EulerNonuniqueness.Section5.CascadeActualCommonBoundaryJointSource
import EulerNonuniqueness.Section5.CascadeBoundaryHistoryContinuity
import EulerNonuniqueness.General.WeightedHistoryIntegral

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance rawSourceWeightedHistoryC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd

open EulerNonuniqueness.General EulerNonuniqueness.Section6 FiniteMovingPatchFamily

theorem exists_uniform_actual_raw_source_weighted_history :
    ∃ rawCap > (0 : ℝ), ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {requestedCap shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair requestedCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      0 < requestedCap → requestedCap ≤ rawCap →
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ (index : Fin count) (patch : Fin 4), ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      ∀ weight : ℝ, 0 < weight →
      let label := finProdFinEquiv (index, patch)
      let first := prepared.referenceWitness.trajectory.spectralCoordinate label
      let final := prepared.trajectory.spectralCoordinate label
      let rawBudget := fun time => ‖diskPhysicalTransverseProjection (first time) - diskPhysicalTransverseProjection (final time)‖ +
        (‖diskPhysicalTransverseProjection (first time)‖ + ‖diskPhysicalTransverseProjection (final time)‖) *
          ‖diskNeutralCLM (first time) - diskNeutralCLM (final time)‖
      weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * rawBudget time) ≤
        constant * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          canonicalExteriorCoefficientPairSeries prepared.referenceWitness.trajectory.movingFamily
            prepared.trajectory.movingFamily label label time := by
  obtain ⟨historyCap, historyPositive, histories⟩ := exists_uniform_actual_common_boundary_joint_source_history
  obtain ⟨continuityCap, continuityPositive, rawContinuity⟩ := exists_uniform_actual_raw_spectral_continuity
  let rawCap := min historyCap continuityCap
  refine ⟨rawCap, lt_min historyPositive continuityPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantOne, radiusCoefficient, _, historyRoot, historyEight, historyParameters⟩ :=
    histories factor factorPositive factorSmall
  obtain ⟨continuityRoot, _, coefficientParameters⟩ :=
    exists_uniform_actual_canonical_boundary_coefficient_continuity factor factorPositive factorSmall
  let rootMin := max historyRoot continuityRoot
  refine ⟨constant ^ 2, by nlinarith only [constantOne], rootMin,
    historyEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  filter_upwards [historyParameters scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity
      ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative,
    coefficientParameters scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity
      ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative]
    with frequency history coefficientContinuity
  intro count orbit sectionTime phase dipoleAngle requestedCap shapeRadius monitor boundaryConstant prepared
    requestedPositive requestedSmall path index patch finish finishNonnegative finishBound weight weightPositive
  dsimp only
  let label := finProdFinEquiv (index, patch)
  let first := prepared.referenceWitness.trajectory.spectralCoordinate label
  let final := prepared.trajectory.spectralCoordinate label
  let rawBudget := fun time => ‖diskPhysicalTransverseProjection (first time) - diskPhysicalTransverseProjection (final time)‖ +
    (‖diskPhysicalTransverseProjection (first time)‖ + ‖diskPhysicalTransverseProjection (final time)‖) *
      ‖diskNeutralCLM (first time) - diskNeutralCLM (final time)‖
  let coefficients := canonicalExteriorCoefficientPairSeries prepared.referenceWitness.trajectory.movingFamily
    prepared.trajectory.movingFamily label label
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  obtain ⟨firstContinuous, finalContinuous⟩ := rawContinuity prepared requestedPositive
    (requestedSmall.trans (min_le_right _ _)) path label
  have rawContinuous : ContinuousOn rawBudget (Icc 0 finish) := by
    have firstOn : ContinuousOn first (Icc 0 finish) := firstContinuous.mono subset
    have finalOn : ContinuousOn final (Icc 0 finish) := finalContinuous.mono subset
    have firstProjection : ContinuousOn (fun time => diskPhysicalTransverseProjection (first time)) (Icc 0 finish) :=
      diskPhysicalTransverseProjection.continuous.comp_continuousOn firstOn
    have finalProjection : ContinuousOn (fun time => diskPhysicalTransverseProjection (final time)) (Icc 0 finish) :=
      diskPhysicalTransverseProjection.continuous.comp_continuousOn finalOn
    have firstNeutral : ContinuousOn (fun time => diskNeutralCLM (first time)) (Icc 0 finish) :=
      diskNeutralCLM.continuous.comp_continuousOn firstOn
    have finalNeutral : ContinuousOn (fun time => diskNeutralCLM (final time)) (Icc 0 finish) :=
      diskNeutralCLM.continuous.comp_continuousOn finalOn
    with_reducible_and_instances
      exact (firstProjection.sub finalProjection).norm.add
        ((firstProjection.norm.add finalProjection.norm).mul (firstNeutral.sub finalNeutral).norm)
  have coefficientsContinuous : ContinuousOn coefficients (Icc 0 finish) :=
    (coefficientContinuity count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index patch).mono subset
  have coefficientsNonnegative (time : ℝ) : 0 ≤ coefficients time := by
    unfold coefficients canonicalExteriorCoefficientPairSeries
    exact tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) :
      rawBudget time ≤ ∫ current in (0 : ℝ)..time, constant ^ 2 * coefficients current := by
    have actual := history count orbit sectionTime phase dipoleAngle prepared requestedPositive
      (requestedSmall.trans (min_le_left _ _)) path index patch time (subset inside)
    have bound := actual.1.trans (mul_le_mul_of_nonneg_left actual.2.2 (zero_le_one.trans constantOne))
    with_reducible_and_instances
      change rawBudget time ≤ constant * (∫ current in (0 : ℝ)..time, constant * coefficients current) at bound
    rw [intervalIntegral.integral_const_mul] at bound
    rw [intervalIntegral.integral_const_mul]
    exact bound.trans_eq (by ring)
  have weighted := weighted_integral_le_of_history_majorant finishNonnegative weightPositive rawContinuous
    (continuousOn_const.mul coefficientsContinuous)
    (fun time _ => mul_nonneg (sq_nonneg constant) (coefficientsNonnegative time)) pointwise
  have integralIdentity :
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (constant ^ 2 * coefficients time)) =
        constant ^ 2 * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * coefficients time := by
    simp_rw [mul_left_comm _ (constant ^ 2)]
    rw [intervalIntegral.integral_const_mul]
  rw [integralIdentity] at weighted
  with_reducible_and_instances
    exact weighted

end EulerNonuniqueness.Paper
