import EulerNonuniqueness.Section5.CascadeActualCommonBoundaryHistory
import EulerNonuniqueness.Section5.CascadeActualCommonRawSourceBudget
import EulerNonuniqueness.Section5.CascadeActualCommonBoundaryInitialTrace

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.General EulerNonuniqueness.Section6 FiniteMovingPatchFamily

local instance actualCommonBoundaryJointSourceC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

private theorem commonBoundaryDistance_radius_comparison
    {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
    (frequency time : ℝ) (first final : PeriodicC1HolderHalf) {firstRadius finalRadius multiplier : ℝ}
    (multiplierOne : 1 ≤ multiplier) (radiusBound : firstRadius ≤ multiplier * finalRadius) :
    family.canonicalExteriorCommonBoundaryDistance index frequency time firstRadius first final ≤
      multiplier * family.canonicalExteriorCommonBoundaryDistance index frequency time finalRadius first final := by
  unfold canonicalExteriorCommonBoundaryDistance weightedBoundaryPairDistance
  have firstBound := le_mul_of_one_le_left
    (norm_nonneg (family.canonicalExteriorCommonQuadraticCoordinate index frequency time (diskPhysicalSpectralChart final) -
      family.canonicalExteriorCommonQuadraticCoordinate index frequency time (diskPhysicalSpectralChart first))) multiplierOne
  have finalBound := mul_le_mul_of_nonneg_right radiusBound
    (norm_nonneg (family.canonicalExteriorCommonTrueAngularCoordinate index frequency time (diskPhysicalSpectralChart final) -
      family.canonicalExteriorCommonTrueAngularCoordinate index frequency time (diskPhysicalSpectralChart first)))
  exact (add_le_add firstBound finalBound).trans_eq (by ring)

theorem exists_uniform_actual_common_boundary_joint_source_history :
    ∃ rawCap > 0, ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ constant ≥ (1 : ℝ), ∃ radiusCoefficient ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {requestedCap shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair requestedCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      0 < requestedCap → requestedCap ≤ rawCap →
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ (index : Fin count) (patch : Fin 4),
      let changed : Scales := {scales with frequency := frequency}
      let label := finProdFinEquiv (index, patch)
      let signedFrequency := patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4
      let radius := radiusCoefficient / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2)
      let distance := fun current => prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonBoundaryDistance label signedFrequency current radius
        (prepared.referenceWitness.trajectory.spectralCoordinate label current) (prepared.trajectory.spectralCoordinate label current)
      let coefficients := canonicalExteriorCoefficientPairSeries prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily label label
      ∀ time ∈ Icc 0 path.stop,
      let first := prepared.referenceWitness.trajectory.spectralCoordinate label time
      let final := prepared.trajectory.spectralCoordinate label time
      (‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖ +
        (‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖) *
          ‖diskNeutralCLM first - diskNeutralCLM final‖ ≤ constant * distance time) ∧
        |signedFrequency| * radius ^ 2 ≤ 1 ∧
        distance time ≤ ∫ current in (0 : ℝ)..time, constant * coefficients current := by
  obtain ⟨historyConstant, historyOne, historyCap, historyCapPositive, histories⟩ :=
    exists_uniform_actual_common_boundary_original_time_history
  obtain ⟨rawConstant, rawOne, rawStateCap, rawStateCapPositive, rawBudgets⟩ :=
    exists_uniform_actual_common_raw_source_budget
  let rawCap := min historyCap rawStateCap
  refine ⟨rawCap, lt_min historyCapPositive rawStateCapPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨historyCoefficient, historyCoefficientOne, historyRoot, historyEight, historyBounds⟩ := histories factor factorPositive factorSmall
  obtain ⟨rawCoefficient, rawCoefficientOne, rawRoot, rawEight, rawBounds⟩ := rawBudgets factor factorPositive factorSmall
  obtain ⟨materialRoot, materialEight, materialBounds⟩ := exists_uniform_actual_common_boundary_material_envelopes factor factorPositive factorSmall
  let sourceConstant := Real.exp historyConstant * historyConstant
  let constant := max sourceConstant (rawConstant * rawCoefficient)
  let rootMin := max historyRoot (max rawRoot (max materialRoot (historyCoefficient ^ 2)))
  have historyNonnegative : 0 ≤ historyConstant := zero_le_one.trans historyOne
  have sourceOne : 1 ≤ sourceConstant := by
    have exponentialOne := Real.one_le_exp_iff.mpr historyNonnegative
    dsimp only [sourceConstant]
    nlinarith only [exponentialOne, historyOne]
  have constantOne : 1 ≤ constant := sourceOne.trans (le_max_left _ _)
  refine ⟨constant, constantOne, historyCoefficient, historyCoefficientOne, rootMin, historyEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  have rootHistory : historyRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have rootRaw : rawRoot ≤ scaleRoot := (le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)
  have rootMaterial : materialRoot ≤ scaleRoot := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans rootLarge))
  have rootSquare : historyCoefficient ^ 2 ≤ scaleRoot := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans rootLarge))
  have rootPositive : 0 < scaleRoot := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) (historyEight.trans rootHistory)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  filter_upwards [historyBounds scales scaleRoot rootHistory amplitudeIdentity ratioLarge alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    rawBounds scales scaleRoot rootRaw amplitudeIdentity ratioLarge alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    materialBounds scales scaleRoot rootMaterial amplitudeIdentity ratioLarge alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative, eventually_ge_atTop (1 : ℝ)]
    with frequency history rawBudget material frequencyOne
  intro count orbit sectionTime phase dipoleAngle requestedCap shapeRadius monitor boundaryConstant prepared requestedPositive requestedSmall path index patch
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let label := finProdFinEquiv (index, patch)
  let omega := changed.omega (index.val + 1)
  let signedFrequency := patchSign patch * changed.amplitude * omega ^ 4
  let radius := historyCoefficient / (scaleRoot ^ 2 * omega ^ 2)
  let rawRadius := rawCoefficient / (scaleRoot ^ 2 * omega ^ 2)
  let distance := fun current => prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonBoundaryDistance label signedFrequency current radius
    (prepared.referenceWitness.trajectory.spectralCoordinate label current) (prepared.trajectory.spectralCoordinate label current)
  let coefficients := canonicalExteriorCoefficientPairSeries prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily label label
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive (by change 0 < scales.ratio; linarith) _
  have radiusNonnegative : 0 ≤ radius := div_nonneg (zero_le_one.trans historyCoefficientOne) (by positivity)
  have signedAbsolute : |signedFrequency| = scaleRoot ^ 3 * omega ^ 4 := by
    dsimp only [signedFrequency]
    rw [← Real.norm_eq_abs, norm_mul, norm_mul, norm_patchSign, one_mul,
      Real.norm_of_nonneg amplitudePositive.le, Real.norm_of_nonneg (by positivity : 0 ≤ omega ^ 4)]
    rw [show changed.amplitude = scaleRoot ^ 3 from amplitudeIdentity]
  have rateIdentity : |signedFrequency| * radius ^ 2 = historyCoefficient ^ 2 / scaleRoot := by
    rw [signedAbsolute]
    dsimp only [radius]
    field_simp [rootPositive.ne', omegaPositive.ne']
    <;> ring
  have rateSmall : |signedFrequency| * radius ^ 2 ≤ 1 := by
    rw [rateIdentity]
    exact (div_le_one rootPositive).mpr rootSquare
  have radiusComparison : rawRadius ≤ rawCoefficient * radius := by
    have numerator := le_mul_of_one_le_right (zero_le_one.trans rawCoefficientOne) historyCoefficientOne
    have divided := div_le_div_of_nonneg_right numerator (by positivity : 0 ≤ scaleRoot ^ 2 * omega ^ 2)
    simpa only [rawRadius, radius, mul_div_assoc] using divided
  have coefficientNonnegative (time : ℝ) : 0 ≤ coefficients time := tsum_nonneg (fun _ => by positivity)
  have coefficientContinuous : ContinuousOn coefficients (Icc 0 path.stop) := by
    intro time inside
    obtain ⟨firstScale, finalScale, firstNear, finalNear⟩ := material count orbit sectionTime phase dipoleAngle
      prepared.toCascadeMaterialPreparedPair path time inside index patch
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
    have firstSourceInside (source : Fin (count * 4)) (_ : source ∈ Finset.univ.erase label) :
        time ∈ Ioo (prepared.referenceWitness.trajectory.movingFamily.patch source).initialTime
          (prepared.referenceWitness.trajectory.movingFamily.patch source).finalTime := globalInside
    have finalSourceInside (source : Fin (count * 4)) (_ : source ∈ Finset.univ.erase label) :
        time ∈ Ioo (prepared.trajectory.movingFamily.patch source).initialTime
          (prepared.trajectory.movingFamily.patch source).finalTime := globalInside
    have firstNonnegative : 0 ≤ changed.referenceLocalExteriorWeight (index.val + 1) :=
      (integral_nonneg (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))).trans firstNear.self_of_nhds.2.1
    have finalNonnegative : 0 ≤ changed.cascadeLocalExteriorWeight factor (index.val + 1) :=
      (integral_nonneg (fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))).trans finalNear.self_of_nhds.2.1
    have actual := prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCoefficientPairSeries_continuousAt_geometric
      prepared.trajectory.movingFamily label label (time := time)
      (firstDistance := changed.length (index.val + 1) / 400)
      (finalDistance := factor * changed.length (index.val + 1) / 400)
      (firstWeight := changed.referenceLocalExteriorWeight (index.val + 1))
      (finalWeight := changed.cascadeLocalExteriorWeight factor (index.val + 1))
      (div_pos (changed.length_pos _) (by norm_num)) (div_pos (mul_pos factorPositive (changed.length_pos _)) (by norm_num))
      firstNonnegative finalNonnegative firstScale finalScale firstSourceInside finalSourceInside firstNear.self_of_nhds.1 finalNear.self_of_nhds.1
      (firstNear.mono fun _ actual => actual.2.1) (finalNear.mono fun _ actual => actual.2.1)
    exact actual.continuousWithinAt
  have historyActual := history count orbit sectionTime phase dipoleAngle prepared requestedPositive
    (requestedSmall.trans (min_le_left _ _)) path index patch
  have rawActual := rawBudget count orbit sectionTime phase dipoleAngle prepared requestedPositive
    (requestedSmall.trans (min_le_right _ _)) path
  have initial : distance 0 = 0 := prepared.commonBoundaryDistance_initial_zero label signedFrequency radius
  intro time inside
  have distanceNonnegative : 0 ≤ distance time := by
    unfold distance canonicalExteriorCommonBoundaryDistance weightedBoundaryPairDistance
    positivity
  have rawBound := rawActual time inside index patch
  have comparison := commonBoundaryDistance_radius_comparison prepared.referenceWitness.trajectory.movingFamily label signedFrequency time
    (prepared.referenceWitness.trajectory.spectralCoordinate label time) (prepared.trajectory.spectralCoordinate label time) rawCoefficientOne radiusComparison
  have jointRaw := rawBound.trans (mul_le_mul_of_nonneg_left comparison (zero_le_one.trans rawOne))
  have rawEnlarged := mul_le_mul_of_nonneg_right (le_max_right sourceConstant (rawConstant * rawCoefficient)) distanceNonnegative
  have rawResult := jointRaw.trans (by simpa only [mul_assoc] using rawEnlarged)
  have actual := (historyActual time inside).2
  with_reducible_and_instances
    change distance time ≤ Real.exp (historyConstant * |signedFrequency| * radius ^ 2 * time) *
      (historyConstant * distance 0 + ∫ current in (0 : ℝ)..time,
        Real.exp (-(historyConstant * |signedFrequency| * radius ^ 2) * current) * (historyConstant * coefficients current)) at actual
  rw [initial, mul_zero, zero_add] at actual
  have coefficientIntegrable := (coefficientContinuous.mono (Icc_subset_Icc le_rfl inside.2)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have dampingContinuous : Continuous (fun current : ℝ => Real.exp (-(historyConstant * |signedFrequency| * radius ^ 2) * current)) := by fun_prop
  have integrable : IntervalIntegrable (fun current => Real.exp (-(historyConstant * |signedFrequency| * radius ^ 2) * current) *
      (historyConstant * coefficients current)) volume 0 time := (dampingContinuous.continuousOn.mul
    (continuousOn_const.mul (coefficientContinuous.mono (Icc_subset_Icc le_rfl inside.2)))).intervalIntegrable_of_Icc (μ := volume) inside.1
  have integralBound := intervalIntegral.integral_mono_on inside.1 integrable (coefficientIntegrable.const_mul historyConstant)
    (fun current member => by
      have damping : Real.exp (-(historyConstant * |signedFrequency| * radius ^ 2) * current) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by have nonnegative := mul_nonneg (mul_nonneg historyNonnegative (mul_nonneg (abs_nonneg signedFrequency) (sq_nonneg radius))) member.1; nlinarith only [nonnegative])
      exact (mul_le_mul_of_nonneg_right damping (mul_nonneg historyNonnegative (coefficientNonnegative current))).trans_eq (one_mul _))
  have exponentBound : historyConstant * |signedFrequency| * radius ^ 2 * time ≤ historyConstant := by
    have first := mul_le_mul_of_nonneg_left rateSmall historyNonnegative
    have next := mul_le_mul_of_nonneg_right first inside.1
    have final := mul_le_mul_of_nonneg_left (inside.2.trans path.stopBound) historyNonnegative
    nlinarith only [next, final]
  have bounded := mul_le_mul (Real.exp_le_exp.mpr exponentBound) integralBound
    (intervalIntegral.integral_nonneg_of_forall inside.1 (fun current => mul_nonneg (Real.exp_pos _).le (mul_nonneg historyNonnegative (coefficientNonnegative current))))
    (Real.exp_pos historyConstant).le
  have sourceResult := actual.trans bounded
  rw [intervalIntegral.integral_const_mul] at sourceResult
  have integralNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time, coefficients current :=
    intervalIntegral.integral_nonneg_of_forall inside.1 coefficientNonnegative
  have enlarged := mul_le_mul_of_nonneg_right (le_max_left sourceConstant (rawConstant * rawCoefficient)) integralNonnegative
  have historyResult : distance time ≤ ∫ current in (0 : ℝ)..time, constant * coefficients current := by
    rw [intervalIntegral.integral_const_mul]
    exact sourceResult.trans (by simpa only [sourceConstant, mul_assoc] using enlarged)
  with_reducible_and_instances
    simpa only [distance, radius, signedFrequency, coefficients, label, omega, changed] using And.intro rawResult (And.intro rateSmall historyResult)

end EulerNonuniqueness.Paper
