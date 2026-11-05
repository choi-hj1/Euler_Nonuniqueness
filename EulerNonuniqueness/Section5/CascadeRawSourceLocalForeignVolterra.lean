import EulerNonuniqueness.Section5.CascadeActualCommonBoundaryJointSource
import EulerNonuniqueness.Section5.CascadeBoundaryHistoryContinuity
import EulerNonuniqueness.Section5.CascadeCanonicalBoundaryLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeForeignPatchCoefficientIntegrability
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.General.ExponentialVolterra

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem raw_local_foreign_volterra
    {raw coefficients center foreign : ℝ → ℝ} {finish constant omega rate : ℝ}
    (ordered : 0 ≤ finish) (constantNonnegative : 0 ≤ constant) (omegaNonnegative : 0 ≤ omega)
    (rateNonnegative : 0 ≤ rate)
    (rawContinuous : ContinuousOn raw (Icc 0 finish)) (coefficientContinuous : ContinuousOn coefficients (Icc 0 finish))
    (centerContinuous : ContinuousOn center (Icc 0 finish))
    (centerNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ center time)
    (foreignNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ foreign time)
    (foreignIntegrable : IntervalIntegrable (fun time => Real.exp (-rate * time) * foreign time) volume 0 finish)
    (history : ∀ time ∈ Icc 0 finish, raw time ≤ ∫ current in (0 : ℝ)..time, coefficients current)
    (coefficientBound : ∀ time ∈ Icc 0 finish,
      coefficients time ≤ constant * omega * center time + rate * raw time + constant * foreign time) :
    ∀ time ∈ Icc 0 finish, raw time ≤ constant * ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * (omega * center current + foreign current) := by
  let residual := fun time => max 0 (coefficients time - rate * raw time)
  have residualContinuous : ContinuousOn residual (Icc 0 finish) :=
    continuousOn_const.sup (coefficientContinuous.sub (continuousOn_const.mul rawContinuous))
  have preliminary (time : ℝ) (inside : time ∈ Icc 0 finish) : raw time ≤
      ∫ current in (0 : ℝ)..time, residual current + rate * raw current := by
    have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    apply (history time inside).trans
    apply intervalIntegral.integral_mono_on inside.1
      ((coefficientContinuous.mono subset).intervalIntegrable_of_Icc (μ := volume) inside.1)
      (((residualContinuous.add (continuousOn_const.mul rawContinuous)).mono subset).intervalIntegrable_of_Icc (μ := volume) inside.1)
    intro current _
    have bound := le_max_right (0 : ℝ) (coefficients current - rate * raw current)
    change _ ≤ max 0 (coefficients current - rate * raw current) + rate * raw current
    linarith only [bound]
  have resolved := exponential_volterra_gronwall (trajectory := raw) (forcing := residual)
    (initial := 0) (rate := 0) (feedback := rate) (multiplier := 1)
    rawContinuous residualContinuous rateNonnegative (by norm_num) ordered
    (by simpa only [zero_mul, Real.exp_zero, mul_one, one_mul, zero_add] using preliminary)
  have residualBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      residual time ≤ constant * (omega * center time + foreign time) := by
    have centerPositive := centerNonnegative time inside
    have foreignPositive := foreignNonnegative time inside
    apply max_le (by positivity)
    have bound := coefficientBound time inside
    nlinarith only [bound]
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have weightedForeign := foreignIntegrable.mono_set (by
    rw [uIcc_of_le inside.1, uIcc_of_le ordered]
    exact subset)
  have kernelForeignIntegrable : IntervalIntegrable
      (fun current => Real.exp (rate * (time - current)) * foreign current) volume 0 time := by
    convert weightedForeign.const_mul (Real.exp (rate * time)) using 1
    ext current
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have kernelContinuous : Continuous (fun current : ℝ => Real.exp (rate * (time - current))) := by fun_prop
  have kernelCenterIntegrable := (kernelContinuous.continuousOn.mul (centerContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have upperIntegrable : IntervalIntegrable (fun current => Real.exp (rate * (time - current)) *
      (constant * (omega * center current + foreign current))) volume 0 time := by
    convert ((kernelCenterIntegrable.const_mul omega).add kernelForeignIntegrable).const_mul constant using 1
    ext current
    ring
  have comparison := intervalIntegral.integral_mono_on inside.1
    ((kernelContinuous.continuousOn.mul (residualContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1)
    upperIntegrable (fun current member => mul_le_mul_of_nonneg_left (residualBound current (subset member)) (Real.exp_pos _).le)
  have actual := (resolved time inside).trans (by
    simpa only [mul_one, zero_add, zero_mul, one_mul] using comparison)
  convert actual using 1
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext current
  ring

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

open FiniteMovingPatchFamily

theorem exists_uniform_actual_raw_source_local_foreign_volterra :
    ∃ rawCap > (0 : ℝ), ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.referenceWitness.trajectory.movingFamily
    let second := prepared.trajectory.movingFamily
    let omega := changed.omega (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let rate := constant * omega * epsilon
    let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time‖
    0 ≤ rate ∧ rate ≤ 1 ∧
    (∀ patch : Fin 4, ∀ time ∈ Icc 0 finish, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time‖)) ∧
    (∀ patch : Fin 4, IntervalIntegrable (foreign patch) volume 0 finish) ∧
    (∀ patch : Fin 4, IntervalIntegrable (fun time => Real.exp (-rate * time) * foreign patch time) volume 0 finish) ∧
    ∀ time ∈ Icc 0 finish, (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤
      constant * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
        (omega * prepared.rawSourceCenteredState current index + ∑ patch : Fin 4, foreign patch current) := by
  obtain ⟨historyCap, historyPositive, histories⟩ := exists_uniform_actual_common_boundary_joint_source_history
  obtain ⟨ownCap, ownPositive, owns⟩ := exists_uniform_actual_canonical_boundary_local_foreign_return
  obtain ⟨patchCap, patchPositive, patches⟩ := exists_uniform_actual_foreign_patch_coefficient_integrability
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min historyCap (min ownCap (min patchCap continuityCap))
  have capPositive : 0 < rawCap := lt_min historyPositive (lt_min ownPositive (lt_min patchPositive continuityPositive))
  have historyCapBound : rawCap ≤ historyCap := min_le_left _ _
  have ownCapBound : rawCap ≤ ownCap := (min_le_right _ _).trans (min_le_left _ _)
  have patchCapBound : rawCap ≤ patchCap := ((min_le_right historyCap _).trans (min_le_right ownCap _)).trans (min_le_left _ _)
  have continuityCapBound : rawCap ≤ continuityCap := ((min_le_right historyCap _).trans (min_le_right ownCap _)).trans (min_le_right _ _)
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨historyConstant, historyOne, radiusCoefficient, radiusCoefficientOne, historyRoot, historyEight, historyFactory⟩ :=
    histories factor factorPositive factorSmall
  obtain ⟨ownConstant, ownNonnegative, ownFactory⟩ := owns factorPositive factorSmall
  obtain ⟨coefficientRoot, coefficientEight, coefficientFactory⟩ :=
    exists_uniform_actual_canonical_boundary_coefficient_continuity factor factorPositive factorSmall
  let constant := 4 * historyConstant ^ 2 * (ownConstant + 1) + 1
  let rootMin := max historyRoot coefficientRoot
  have constantOne : 1 ≤ constant := by
    dsimp only [constant]
    have product := mul_nonneg (sq_nonneg historyConstant) (show 0 ≤ ownConstant + 1 by linarith only [ownNonnegative])
    nlinarith only [product]
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  have historyNonnegative : 0 ≤ historyConstant := zero_le_one.trans historyOne
  have localCoefficient : 4 * historyConstant ^ 2 * ownConstant ≤ constant := by dsimp only [constant]; nlinarith only [sq_nonneg historyConstant]
  have foreignCoefficient : historyConstant ^ 2 ≤ constant := by
    dsimp only [constant]
    nlinarith only [mul_nonneg (sq_nonneg historyConstant) ownNonnegative, sq_nonneg historyConstant]
  refine ⟨constant, constantOne, rootMin, historyEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
    thresholdSmall referenceNonnegative boundaryOne orbit sectionTime
  have rootEight : 8 ≤ scaleRoot := (historyEight.trans (le_max_left _ _)).trans rootLarge
  have rootOne : 1 ≤ scaleRoot := by linarith only [rootEight]
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  filter_upwards [historyFactory scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    coefficientFactory scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    ownFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    patches scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / (100000 * 96)),
    eventually_ge_atTop (max (1 : ℝ) (2 * constant / scales.amplitude + 1))]
    with frequency historyEstimate coefficientContinuity ownEstimate patchEstimate radii lengths frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path index finish finishNonnegative finishBound
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily
  let second := prepared.trajectory.movingFamily
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let rate := constant * omega * epsilon
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let center := fun time => prepared.rawSourceCenteredState time index
  let coefficients := fun patch => canonicalExteriorCoefficientPairSeries first second
    (finProdFinEquiv (index, patch)) (finProdFinEquiv (index, patch))
  let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time‖
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lengthPositive := changed.length_pos (index.val + 1)
  have omegaFrequency : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _
  have omegaOne : 1 ≤ omega := frequencyOne.trans omegaFrequency
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have rateIdentity : rate = 2 * constant / (changed.amplitude * omega ^ 2) := by
    dsimp only [rate, epsilon]
    rw [changed.radius_sq amplitudePositive frequencyPositive ratioPositive]
    field_simp [(changed.length_pos (index.val + 1)).ne', amplitudePositive.ne', omegaPositive.ne']
    ring
  have rateSmall : rate ≤ 1 := by
    rw [rateIdentity]
    apply (div_le_one (show 0 < changed.amplitude * omega ^ 2 by positivity)).mpr
    have lower : 2 * constant / changed.amplitude + 1 ≤ omega := (le_max_right _ _).trans (frequencyLarge.trans omegaFrequency)
    have scaled := (div_le_iff₀ amplitudePositive).mp (show 2 * constant / changed.amplitude ≤ omega by linarith only [lower])
    nlinarith only [scaled, mul_nonneg amplitudePositive.le (mul_nonneg omegaPositive.le (sub_nonneg.mpr omegaOne))]
  have rawPatchNonnegative (patch : Fin 4) (time : ℝ) : 0 ≤ prepared.rawSourceShapeBudget time index patch := by
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have rawNonnegative (time : ℝ) : 0 ≤ raw time := Finset.sum_nonneg (fun patch _ => rawPatchNonnegative patch time)
  have centerNonnegative (time : ℝ) : 0 ≤ center time := by dsimp only [center, CascadeSourcePreparedPair.rawSourceCenteredState]; positivity
  have foreignNonnegative (patch : Fin 4) (time : ℝ) : 0 ≤ foreign patch time := tsum_nonneg (fun _ => by positivity)
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum _ (fun patch _ =>
    ((stateContinuity prepared capPositive continuityCapBound path index).1 patch).mono subset)
  have centerContinuous : ContinuousOn center (Icc 0 finish) := (stateContinuity prepared capPositive continuityCapBound path index).2.1.mono subset
  have coefficientContinuous (patch : Fin 4) : ContinuousOn (coefficients patch) (Icc 0 finish) :=
    (coefficientContinuity count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index patch).mono subset
  have radiusSmall : changed.radius (index.val + 1) ≤ scales.location (index.val + 1) / (100000 * 96) := by
    exact (radii (index.val + 1)).le.trans (by simpa only [one_mul, div_eq_mul_inv, mul_comm] using (lengths (index.val + 1)).le)
  let patchPrepared := prepared.enlargeCap patchCapBound
  have physical (patch : Fin 4) (weight : ℝ) := patchEstimate count phase dipoleAngle patchPrepared path (index, patch)
    (changed.radius (index.val + 1)) (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le
    radiusSmall finish finishNonnegative finishBound weight
  have physicalAtWeight (patch : Fin 4) (weight : ℝ) :
      IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish := by
    have actual := (physical patch weight).2.2
    let opposite := fun time => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time -
        first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time‖
    change IntervalIntegrable (fun time => Real.exp (-weight * time) * opposite time) volume 0 finish at actual
    have identity : opposite = foreign patch := by
      funext time
      dsimp only [opposite, foreign]
      apply tsum_congr
      intro power
      exact congrArg (fun value : ℝ => (96 : ℝ) ^ (power + 1) * value) (norm_sub_rev _ _)
    rw [identity] at actual
    exact actual
  have physicalI (patch : Fin 4) : IntervalIntegrable (foreign patch) volume 0 finish := by
    simpa only [zero_mul, neg_zero, Real.exp_zero, one_mul] using physicalAtWeight patch 0
  have weightedPhysicalI (patch : Fin 4) : IntervalIntegrable (fun time => Real.exp (-rate * time) * foreign patch time) volume 0 finish :=
    physicalAtWeight patch rate
  have physicalSummable (patch : Fin 4) (time : ℝ) (inside : time ∈ Icc 0 finish) := (ownEstimate count phase dipoleAngle
    (prepared.enlargeCap ownCapBound) path (subset inside) (index, patch)).1
  have history (time : ℝ) (inside : time ∈ Icc 0 finish) :
      raw time ≤ ∫ current in (0 : ℝ)..time, historyConstant ^ 2 * ∑ patch : Fin 4, coefficients patch current := by
    have individual (patch : Fin 4) : prepared.rawSourceShapeBudget time index patch ≤
        historyConstant ^ 2 * ∫ current in (0 : ℝ)..time, coefficients patch current := by
      have actual := historyEstimate count orbit sectionTime phase dipoleAngle prepared capPositive historyCapBound path index patch time (subset inside)
      have bound := actual.1.trans (mul_le_mul_of_nonneg_left actual.2.2 historyNonnegative)
      with_reducible_and_instances
        dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget, coefficients, first, second] at bound ⊢
        rw [intervalIntegral.integral_const_mul] at bound
        exact bound.trans_eq (by ring)
    have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => individual patch)
    rw [← Finset.mul_sum] at summed
    have integralIdentity : (∫ current in (0 : ℝ)..time, historyConstant ^ 2 * ∑ patch : Fin 4, coefficients patch current) =
        historyConstant ^ 2 * ∑ patch : Fin 4, ∫ current in (0 : ℝ)..time, coefficients patch current := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      exact intervalIntegral.integral_finset_sum (fun patch _ => ((coefficientContinuous patch).mono
        (Icc_subset_Icc le_rfl inside.2)).intervalIntegrable_of_Icc (μ := volume) inside.1)
    exact summed.trans_eq integralIdentity.symm
  have coefficientBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      historyConstant ^ 2 * (∑ patch : Fin 4, coefficients patch time) ≤
        constant * omega * center time + rate * raw time + constant * ∑ patch : Fin 4, foreign patch time := by
    have individual (patch : Fin 4) : coefficients patch time ≤
        ownConstant * omega * (center time + epsilon * raw time) + foreign patch time := by
      have actual := (ownEstimate count phase dipoleAngle (prepared.enlargeCap ownCapBound) path (subset inside) (index, patch)).2.2
      have rawSum : (∑ other ∈ Finset.univ.erase patch, prepared.rawSourceShapeBudget time index other) ≤ raw time :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun other _ _ => rawPatchNonnegative other time)
      have normalized : coefficients patch time ≤ ownConstant * omega *
          (center time + epsilon * ∑ other ∈ Finset.univ.erase patch, prepared.rawSourceShapeBudget time index other) + foreign patch time := by
        with_reducible_and_instances
          dsimp only [coefficients, first, second, center, foreign, omega, epsilon, CascadeSourcePreparedPair.enlargeCap,
            CascadeSourcePreparedPair.rawSourceCenteredState, CascadeSourcePreparedPair.rawSourceShapeBudget,
            MovingCentroidGaugeTrajectory.spectralCoordinate] at actual ⊢
          exact actual
      apply normalized.trans
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg ownNonnegative omegaPositive.le)
      exact add_le_add_left (mul_le_mul_of_nonneg_left rawSum epsilonNonnegative) _
    have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => individual patch)
    rw [Finset.sum_add_distrib, Finset.sum_const] at summed
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at summed
    have scaled := mul_le_mul_of_nonneg_left summed (sq_nonneg historyConstant)
    have centerPositive := centerNonnegative time
    have rawPositive := rawNonnegative time
    have localBound := mul_le_mul_of_nonneg_right localCoefficient
      (show 0 ≤ omega * (center time + epsilon * raw time) by positivity)
    have forcing := mul_le_mul_of_nonneg_right foreignCoefficient
      (show 0 ≤ ∑ patch : Fin 4, foreign patch time from Finset.sum_nonneg (fun patch _ => foreignNonnegative patch time))
    dsimp only [rate]
    nlinarith only [scaled, localBound, forcing]
  have foreignSumI : IntervalIntegrable (fun time => Real.exp (-rate * time) * ∑ patch : Fin 4, foreign patch time) volume 0 finish := by
    have finite := IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := finish) Finset.univ
      (f := fun (patch : Fin 4) (time : ℝ) => Real.exp (-rate * time) * foreign patch time) (fun patch _ => weightedPhysicalI patch)
    simpa only [Finset.mul_sum] using finite
  refine ⟨rateNonnegative, rateSmall, ?_, physicalI, weightedPhysicalI, ?_⟩
  · intro patch time inside
    simpa only [first, second, CascadeSourcePreparedPair.enlargeCap] using physicalSummable patch time inside
  · exact raw_local_foreign_volterra (raw := raw) (coefficients := fun time => historyConstant ^ 2 * ∑ patch : Fin 4, coefficients patch time)
      (center := center) (foreign := fun time => ∑ patch : Fin 4, foreign patch time)
      finishNonnegative constantNonnegative omegaPositive.le rateNonnegative rawContinuous
      (continuousOn_const.mul (continuousOn_finset_sum _ (fun patch _ => coefficientContinuous patch))) centerContinuous
      (fun time _ => centerNonnegative time) (fun time _ => Finset.sum_nonneg (fun patch _ => foreignNonnegative patch time))
      foreignSumI history coefficientBound

end EulerNonuniqueness.Paper
