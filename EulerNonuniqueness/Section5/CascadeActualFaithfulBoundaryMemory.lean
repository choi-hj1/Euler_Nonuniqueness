import EulerNonuniqueness.Section5.CascadeActualCommonBoundaryJointSource
import EulerNonuniqueness.Section5.CascadeBoundaryHistoryContinuity
import EulerNonuniqueness.Section5.CascadeCanonicalBoundaryLocalForeignReturn
import EulerNonuniqueness.Section5.CascadePhysicalForeignForcingContinuity
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.General.ExponentialVolterra

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

private theorem faithful_kernel_identity (forcing : ℝ → ℝ) (rate start finish : ℝ) :
    (∫ current in start..finish, Real.exp (rate * (finish - current)) * forcing current) =
      Real.exp (rate * finish) * ∫ current in start..finish, Real.exp (-rate * current) * forcing current := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro current _
  change Real.exp (rate * (finish - current)) * forcing current =
    Real.exp (rate * finish) * (Real.exp (-rate * current) * forcing current)
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem faithful_memory_properties {forcing : ℝ → ℝ} {horizon constant rate : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (constantNonnegative : 0 ≤ constant)
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (forcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time) :
    let memory := fun time => constant * ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * forcing current
    ContinuousOn memory (Icc 0 horizon) ∧
      IntervalIntegrable memory volume 0 horizon ∧ memory 0 = 0 ∧
      (∀ time ∈ Icc 0 horizon, 0 ≤ memory time) ∧
      ∀ start ∈ Icc 0 horizon, ∀ finish ∈ Icc start horizon,
        memory finish = Real.exp (rate * (finish - start)) * memory start +
          constant * ∫ current in start..finish, Real.exp (rate * (finish - current)) * forcing current := by
  dsimp only
  let weighted := fun current => Real.exp (-rate * current) * forcing current
  have exponential : Continuous (fun current : ℝ => Real.exp (-rate * current)) := by fun_prop
  have weightedContinuous : ContinuousOn weighted (Icc 0 horizon) :=
    exponential.continuousOn.mul forcingContinuous
  have weightedIntegrable := weightedContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have primitiveContinuous : ContinuousOn (fun time => ∫ current in (0 : ℝ)..time, weighted current) (Icc 0 horizon) := by
    simpa only [uIcc_of_le horizonNonnegative] using
      intervalIntegral.continuousOn_primitive_interval' weightedIntegrable left_mem_uIcc
  have memoryContinuous : ContinuousOn (fun time => constant * ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * forcing current) (Icc 0 horizon) := by
    simp_rw [faithful_kernel_identity]
    exact continuousOn_const.mul ((by fun_prop : Continuous (fun time : ℝ => Real.exp (rate * time))).continuousOn.mul primitiveContinuous)
  refine ⟨memoryContinuous, memoryContinuous.intervalIntegrable_of_Icc horizonNonnegative, by simp, ?_, ?_⟩
  · intro time inside
    exact mul_nonneg constantNonnegative (intervalIntegral.integral_nonneg inside.1 fun current member =>
      mul_nonneg (Real.exp_pos _).le (forcingNonnegative current ⟨member.1, member.2.trans inside.2⟩))
  · intro start startInside finish finishInside
    have firstIntegrable := (weightedContinuous.mono (Icc_subset_Icc le_rfl startInside.2)).intervalIntegrable_of_Icc (μ := volume) startInside.1
    have secondIntegrable := (weightedContinuous.mono (Icc_subset_Icc startInside.1 finishInside.2)).intervalIntegrable_of_Icc (μ := volume) finishInside.1
    have split := intervalIntegral.integral_add_adjacent_intervals firstIntegrable secondIntegrable
    simp_rw [faithful_kernel_identity]
    change constant * (Real.exp (rate * finish) * ∫ current in (0 : ℝ)..finish, weighted current) = _
    rw [← split]
    have product : Real.exp (rate * (finish - start)) * Real.exp (rate * start) = Real.exp (rate * finish) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change constant * (Real.exp (rate * finish) *
      ((∫ current in (0 : ℝ)..start, weighted current) + ∫ current in start..finish, weighted current)) =
      Real.exp (rate * (finish - start)) *
        (constant * (Real.exp (rate * start) * ∫ current in (0 : ℝ)..start, weighted current)) +
        constant * (Real.exp (rate * finish) * ∫ current in start..finish, weighted current)
    rw [show Real.exp (rate * (finish - start)) *
        (constant * (Real.exp (rate * start) * ∫ current in (0 : ℝ)..start, weighted current)) =
      constant * (Real.exp (rate * (finish - start)) * Real.exp (rate * start)) *
        (∫ current in (0 : ℝ)..start, weighted current) by ring, product]
    ring

theorem exists_uniform_actual_faithful_boundary_memory :
    ∃ rawCap > (0 : ℝ), ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ constant ≥ (1 : ℝ), ∃ radiusCoefficient ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ,
      threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {requestedCap shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair requestedCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    0 < requestedCap → requestedCap ≤ rawCap →
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ index : Fin count,
    let changed : Scales := {scales with frequency := frequency}
    let omega := changed.omega (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let radius := radiusCoefficient / (scaleRoot ^ 2 * omega ^ 2)
    let distance := fun time => ∑ patch : Fin 4,
      prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonBoundaryDistance
        (finProdFinEquiv (index, patch)) (patchSign patch * changed.amplitude * omega ^ 4) time radius
        (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)
        (prepared.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)
    let drive := fun time => omega * prepared.rawSourceCenteredState time index + prepared.physicalForeignSourceForcing index time
    let rate := constant * (1 + omega * epsilon)
    let memory := fun time => constant * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * drive current
    ContinuousOn memory (Icc 0 path.stop) ∧ IntervalIntegrable memory volume 0 path.stop ∧
      memory 0 = 0 ∧ distance 0 = 0 ∧
      (∀ time ∈ Icc 0 path.stop, 0 ≤ memory time ∧ distance time ≤ memory time ∧
        (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤ constant * memory time) ∧
      ∀ start ∈ Icc 0 path.stop, ∀ finish ∈ Icc start path.stop,
        memory finish = Real.exp (rate * (finish - start)) * memory start +
          constant * ∫ current in start..finish, Real.exp (rate * (finish - current)) * drive current := by
  obtain ⟨jointCap, jointPositive, jointParameters⟩ := exists_uniform_actual_common_boundary_joint_source_history
  obtain ⟨pointCap, pointPositive, pointParameters⟩ := exists_uniform_actual_canonical_boundary_local_foreign_return
  obtain ⟨stateCap, statePositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min jointCap (min pointCap stateCap)
  refine ⟨rawCap, lt_min jointPositive (lt_min pointPositive statePositive), ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨historyConstant, historyOne, radiusCoefficient, radiusOne, historyRoot, historyEight, historyParameters⟩ :=
    jointParameters factor factorPositive factorSmall
  obtain ⟨ownConstant, ownNonnegative, pointBounds⟩ := pointParameters factorPositive factorSmall
  obtain ⟨continuousRoot, continuousEight, coefficientParameters⟩ :=
    exists_uniform_actual_canonical_boundary_coefficient_continuity factor factorPositive factorSmall
  let constant := 4 * historyConstant ^ 2 * (ownConstant + 1) + 4 * historyConstant * (ownConstant + 1) + historyConstant + 1
  have historyNonnegative : 0 ≤ historyConstant := zero_le_one.trans historyOne
  have firstNonnegative : 0 ≤ 4 * historyConstant ^ 2 * (ownConstant + 1) := by positivity
  have secondNonnegative : 0 ≤ 4 * historyConstant * (ownConstant + 1) := by positivity
  have constantOne : 1 ≤ constant := by
    dsimp only [constant]
    linarith only [firstNonnegative, secondNonnegative, historyNonnegative]
  have constantHistory : historyConstant ≤ constant := by
    dsimp only [constant]
    linarith only [firstNonnegative, secondNonnegative]
  have constantCenter : 4 * historyConstant * ownConstant ≤ constant := by
    dsimp only [constant]
    nlinarith only [sq_nonneg historyConstant, mul_nonneg (sq_nonneg historyConstant) ownNonnegative, historyNonnegative]
  have constantFeedback : 4 * historyConstant ^ 2 * ownConstant ≤ constant := by
    dsimp only [constant]
    nlinarith only [sq_nonneg historyConstant, mul_nonneg historyNonnegative ownNonnegative, historyNonnegative]
  let rootMin := max historyRoot continuousRoot
  refine ⟨constant, constantOne, radiusCoefficient, radiusOne, rootMin, historyEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
    thresholdSmall referenceNonnegative boundaryOne orbit sectionTime
  have rootHistory : historyRoot ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have rootContinuous : continuousRoot ≤ scaleRoot := (le_max_right _ _).trans rootLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (historyEight.trans rootHistory)
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  filter_upwards [historyParameters scales scaleRoot rootHistory amplitudeIdentity ratioBound alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    pointBounds scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne,
    coefficientParameters scales scaleRoot rootContinuous amplitudeIdentity ratioBound alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    scales.eventually_cascade_physical_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_ge_atTop (1 : ℝ)] with frequency histories points coefficientContinuity foreignContinuity frequencyOne
  intro count phase dipoleAngle requestedCap shapeRadius monitor prepared requestedPositive requestedSmall path index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let radius := radiusCoefficient / (scaleRoot ^ 2 * omega ^ 2)
  let distance := fun time => ∑ patch : Fin 4,
    prepared.referenceWitness.trajectory.movingFamily.canonicalExteriorCommonBoundaryDistance
      (finProdFinEquiv (index, patch)) (patchSign patch * changed.amplitude * omega ^ 4) time radius
      (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)
      (prepared.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)
  let coefficients := fun time => ∑ patch : Fin 4,
    canonicalExteriorCoefficientPairSeries prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily
      (finProdFinEquiv (index, patch)) (finProdFinEquiv (index, patch)) time
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let centered := fun time => prepared.rawSourceCenteredState time index
  let foreign := prepared.physicalForeignSourceForcing index
  let drive := fun time => omega * centered time + foreign time
  let rate := constant * (1 + omega * epsilon)
  let primitive := fun time => historyConstant * ∫ current in (0 : ℝ)..time, coefficients current
  let memory := fun time => constant * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * drive current
  have omegaPositive : 0 < omega := changed.omega_pos (zero_lt_one.trans_le frequencyOne)
    (by change 0 < scales.ratio; linarith only [ratioBound]) _
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have coefficientContinuous : ContinuousOn coefficients (Icc 0 path.stop) :=
    continuousOn_finset_sum _ fun patch _ =>
      coefficientContinuity count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index patch
  have coefficientNonnegative (time : ℝ) : 0 ≤ coefficients time := by
    apply Finset.sum_nonneg
    intro patch _
    exact tsum_nonneg fun _ => by positivity
  have primitiveContinuous : ContinuousOn primitive (Icc 0 path.stop) := by
    have actual := intervalIntegral.continuousOn_primitive_interval'
      (coefficientContinuous.intervalIntegrable_of_Icc (μ := volume) path.stopPositive.le) left_mem_uIcc
    have normalized : ContinuousOn (fun time => ∫ current in (0 : ℝ)..time, coefficients current) (Icc 0 path.stop) := by
      simpa only [uIcc_of_le path.stopPositive.le] using actual
    exact continuousOn_const.mul normalized
  have primitiveNonnegative (time : ℝ) (inside : time ∈ Icc 0 path.stop) : 0 ≤ primitive time :=
    mul_nonneg historyNonnegative (intervalIntegral.integral_nonneg inside.1 fun current _ => coefficientNonnegative current)
  have stateActual := stateContinuity prepared requestedPositive
    (requestedSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) path index
  have centeredContinuous : ContinuousOn centered (Icc 0 path.stop) := stateActual.2.1
  have foreignActual := foreignContinuity count phase dipoleAngle prepared path index
  have driveContinuous : ContinuousOn drive (Icc 0 path.stop) :=
    (continuousOn_const.mul centeredContinuous).add foreignActual.2.1
  have centeredNonnegative (time : ℝ) : 0 ≤ centered time :=
    div_nonneg (norm_nonneg _) (changed.length_pos _).le
  have driveNonnegative (time : ℝ) : 0 ≤ drive time :=
    add_nonneg (mul_nonneg omegaPositive.le (centeredNonnegative time)) (prepared.physicalForeignSourceForcing_nonneg index time)
  have historyActual (patch : Fin 4) := histories count orbit sectionTime phase dipoleAngle prepared requestedPositive
    (requestedSmall.trans (min_le_left _ _)) path index patch
  have distancePrimitive (time : ℝ) (inside : time ∈ Icc 0 path.stop) : distance time ≤ primitive time := by
    have summed := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) fun patch _ => (historyActual patch time inside).2.2
    have coefficientIntegrable (patch : Fin 4) := (coefficientContinuity count orbit sectionTime phase dipoleAngle
      prepared.toCascadeMaterialPreparedPair path index patch).mono (Icc_subset_Icc le_rfl inside.2)
      |>.intervalIntegrable_of_Icc (μ := volume) inside.1
    rw [← intervalIntegral.integral_finset_sum (fun patch _ => (coefficientIntegrable patch).const_mul historyConstant)] at summed
    simp_rw [← Finset.mul_sum] at summed
    simpa only [primitive, intervalIntegral.integral_const_mul] using summed
  have rawDistance (time : ℝ) (inside : time ∈ Icc 0 path.stop) : raw time ≤ historyConstant * distance time := by
    have summed := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) fun patch _ => (historyActual patch time inside).1
    with_reducible_and_instances
      simpa only [raw, distance, CascadeSourcePreparedPair.rawSourceShapeBudget, ← Finset.mul_sum] using summed
  have rawPrimitive (time : ℝ) (inside : time ∈ Icc 0 path.stop) : raw time ≤ historyConstant * primitive time :=
    (rawDistance time inside).trans (mul_le_mul_of_nonneg_left (distancePrimitive time inside) historyNonnegative)
  let pointPrepared := prepared.enlargeCap (requestedSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have coefficientBound (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      coefficients time ≤ 4 * ownConstant * omega * (centered time + epsilon * raw time) + foreign time := by
    have each (patch : Fin 4) :
        canonicalExteriorCoefficientPairSeries prepared.referenceWitness.trajectory.movingFamily prepared.trajectory.movingFamily
          (finProdFinEquiv (index, patch)) (finProdFinEquiv (index, patch)) time ≤
        ownConstant * omega * (centered time + epsilon * raw time) +
          (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
            ‖prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
                (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
                (changed.radius (index.val + 1)) (power + 1) time -
              prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
                (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch)
                (changed.radius (index.val + 1)) (power + 1) time‖) := by
      have actual := (points count phase dipoleAngle pointPrepared path inside (index, patch)).2.2
      have erased : (∑ other ∈ Finset.univ.erase patch, prepared.rawSourceShapeBudget time index other) ≤ raw time :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun other _ _ => by dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity)
      have centerInvariant : pointPrepared.rawSourceCenteredState time index = centered time := by
        with_reducible_and_instances
          dsimp only [pointPrepared, CascadeSourcePreparedPair.enlargeCap, centered,
            CascadeSourcePreparedPair.rawSourceCenteredState]
      have rawInvariant (other : Fin 4) : pointPrepared.rawSourceShapeBudget time index other =
          prepared.rawSourceShapeBudget time index other := by
        with_reducible_and_instances
          dsimp only [pointPrepared, CascadeSourcePreparedPair.enlargeCap,
            CascadeSourcePreparedPair.rawSourceShapeBudget]
      rw [centerInvariant] at actual
      simp_rw [rawInvariant] at actual
      with_reducible_and_instances
        change _ ≤ ownConstant * omega * (centered time + epsilon *
          ∑ other ∈ Finset.univ.erase patch, prepared.rawSourceShapeBudget time index other) + _ at actual
      exact actual.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left erased epsilonNonnegative) _)
          (mul_nonneg ownNonnegative omegaPositive.le)) _)
    have summed := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) fun patch _ => each patch
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at summed
    have foreignIdentity : (∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
            (changed.radius (index.val + 1)) (power + 1) time -
          prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch)
            (changed.radius (index.val + 1)) (power + 1) time‖) = foreign time := by
      simp only [foreign, CascadeSourcePreparedPair.physicalForeignSourceForcing, changed, norm_sub_rev]
    rw [foreignIdentity] at summed
    convert summed using 1; ring
  have differentialMajorant (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      historyConstant * coefficients time ≤ constant * drive time + rate * primitive time := by
    have first := mul_le_mul_of_nonneg_left (coefficientBound time inside) historyNonnegative
    have rawScaled := mul_le_mul_of_nonneg_left (rawPrimitive time inside)
      (show 0 ≤ 4 * historyConstant * ownConstant * omega * epsilon by positivity)
    have centerScaled := mul_le_mul_of_nonneg_right constantCenter
      (mul_nonneg omegaPositive.le (centeredNonnegative time))
    have foreignScaled := mul_le_mul_of_nonneg_right constantHistory
      (prepared.physicalForeignSourceForcing_nonneg index time)
    have feedbackScaled := mul_le_mul_of_nonneg_right constantFeedback
      (mul_nonneg (mul_nonneg omegaPositive.le epsilonNonnegative) (primitiveNonnegative time inside))
    have slack := mul_nonneg (zero_le_one.trans constantOne) (primitiveNonnegative time inside)
    dsimp only [drive, rate]
    nlinarith only [first, rawScaled, centerScaled, foreignScaled, feedbackScaled, slack]
  have inequality (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      primitive time ≤ 0 * Real.exp (0 * time) + 1 * ∫ current in (0 : ℝ)..time,
        Real.exp (0 * (time - current)) * (constant * drive current + rate * primitive current) := by
    simp only [zero_mul, Real.exp_zero, one_mul, zero_add]
    rw [show primitive time = ∫ current in (0 : ℝ)..time, historyConstant * coefficients current by
      dsimp only [primitive]; rw [intervalIntegral.integral_const_mul]]
    apply intervalIntegral.integral_mono_on inside.1
      ((continuousOn_const.mul coefficientContinuous).mono (Icc_subset_Icc le_rfl inside.2) |>.intervalIntegrable_of_Icc inside.1)
      (((continuousOn_const.mul driveContinuous).add (continuousOn_const.mul primitiveContinuous)).mono
        (Icc_subset_Icc le_rfl inside.2) |>.intervalIntegrable_of_Icc inside.1)
    intro current member
    exact differentialMajorant current ⟨member.1, member.2.trans inside.2⟩
  have resolved := EulerNonuniqueness.exponential_volterra_gronwall primitiveContinuous
    (continuousOn_const.mul driveContinuous) rateNonnegative (by norm_num : (0 : ℝ) ≤ 1) path.stopPositive.le inequality
  have primitiveMemory (time : ℝ) (inside : time ∈ Icc 0 path.stop) : primitive time ≤ memory time := by
    have actual := resolved time inside
    simp only [zero_add, one_mul, zero_mul, add_zero] at actual
    convert actual using 1
    dsimp only [memory]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro current _
    ring
  have properties := faithful_memory_properties (rate := rate) path.stopPositive.le (zero_le_one.trans constantOne)
    driveContinuous (fun time _ => driveNonnegative time)
  change ContinuousOn memory (Icc 0 path.stop) ∧ IntervalIntegrable memory volume 0 path.stop ∧ memory 0 = 0 ∧ _ at properties
  refine ⟨properties.1, properties.2.1, properties.2.2.1, ?_, ?_, properties.2.2.2.2⟩
  · dsimp only [distance]
    simp only [prepared.commonBoundaryDistance_initial_zero, Finset.sum_const_zero]
  · intro time inside
    have memoryNonnegative := properties.2.2.2.1 time inside
    refine ⟨memoryNonnegative, (distancePrimitive time inside).trans (primitiveMemory time inside), ?_⟩
    exact (rawPrimitive time inside).trans
      ((mul_le_mul_of_nonneg_left (primitiveMemory time inside) historyNonnegative).trans
        (mul_le_mul_of_nonneg_right constantHistory memoryNonnegative))

end EulerNonuniqueness.Paper

