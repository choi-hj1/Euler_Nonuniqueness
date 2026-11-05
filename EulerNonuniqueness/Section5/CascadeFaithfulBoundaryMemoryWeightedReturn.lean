import EulerNonuniqueness.Section5.CascadeActualFaithfulBoundaryMemory
import EulerNonuniqueness.General.WeightedResponseIntegral

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem faithful_centered_state_continuous
    {rawCap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair) (index : Fin count) :
    ContinuousOn (fun time => prepared.rawSourceCenteredState time index) (Icc 0 path.stop) := by
  let first := prepared.referenceWitness.trajectory.movingFamily
  let final := prepared.trajectory.movingFamily
  have centroidContinuous (family : FiniteMovingPatchFamily (count * 4))
      (interior : ∀ label, Icc (0 : ℝ) path.stop ⊆ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (patch : Fin 4) :
      ContinuousOn (fun time => patchCentroid family.patchMotion time index patch) (Icc 0 path.stop) := by
    simp_rw [FiniteMovingPatchFamily.patchCentroid_eq]
    exact fun time inside => ((family.patch _).centroid_contDiffAt (interior _ inside)).continuousAt.continuousWithinAt
  have firstInterior (label : Fin (count * 4)) :
      Icc (0 : ℝ) path.stop ⊆ Ioo (first.patch label).initialTime (first.patch label).finalTime := by
    intro time inside
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have finalInterior (label : Fin (count * 4)) :
      Icc (0 : ℝ) path.stop ⊆ Ioo (final.patch label).initialTime (final.patch label).finalTime := by
    intro time inside
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have firstCenter : ContinuousOn (fun time => quadrupoleCenter first.patchMotion time index) (Icc 0 path.stop) :=
    (continuousOn_finset_sum _ fun patch _ => centroidContinuous first firstInterior patch).div_const 4
  have finalCenter : ContinuousOn (fun time => quadrupoleCenter final.patchMotion time index) (Icc 0 path.stop) :=
    (continuousOn_finset_sum _ fun patch _ => centroidContinuous final finalInterior patch).div_const 4
  have arrayContinuous : ContinuousOn (fun time =>
      (fun patch => patchCentroid first.patchMotion time index patch - quadrupoleCenter first.patchMotion time index) -
      (fun patch => patchCentroid final.patchMotion time index patch - quadrupoleCenter final.patchMotion time index))
      (Icc 0 path.stop) :=
    continuousOn_pi.mpr fun patch => ((centroidContinuous first firstInterior patch).sub firstCenter).sub
      ((centroidContinuous final finalInterior patch).sub finalCenter)
  exact arrayContinuous.norm.div_const _

theorem exists_uniform_actual_faithful_boundary_memory_weighted_return :
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
    (ContinuousOn memory (Icc 0 path.stop) ∧ IntervalIntegrable memory volume 0 path.stop ∧
      memory 0 = 0 ∧ distance 0 = 0 ∧
      (∀ time ∈ Icc 0 path.stop, 0 ≤ memory time ∧ distance time ≤ memory time ∧
        (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤ constant * memory time) ∧
      ∀ start ∈ Icc 0 path.stop, ∀ finish ∈ Icc start path.stop,
        memory finish = Real.exp (rate * (finish - start)) * memory start +
          constant * ∫ current in start..finish, Real.exp (rate * (finish - current)) * drive current) ∧ rate ≤ 2 * constant ∧ rate ≤ omega / 2 ∧
      ∀ finish ∈ Icc 0 path.stop, ∀ weight : ℝ, omega ≤ weight →
        IntervalIntegrable (fun time => Real.exp (-weight * time) * memory time) volume 0 finish ∧
        IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) volume 0 finish ∧
        IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.physicalForeignSourceForcing index time) volume 0 finish ∧
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * memory time) ≤
          (2 * constant / weight) *
            (omega * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
              ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.physicalForeignSourceForcing index time) := by
  obtain ⟨rawCap, rawPositive, parameters⟩ := exists_uniform_actual_faithful_boundary_memory
  refine ⟨rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantOne, radiusCoefficient, radiusOne, rootMin, rootEight, factory⟩ :=
    parameters factor factorPositive factorSmall
  refine ⟨constant, constantOne, radiusCoefficient, radiusOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
    thresholdSmall referenceNonnegative boundaryOne orbit sectionTime
  have rootBound : 8 ≤ scaleRoot := rootEight.trans rootLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans rootBound
  have amplitudeTwo : 2 ≤ scales.amplitude := by
    rw [amplitudeIdentity]
    have cubic := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) rootBound 3
    norm_num at cubic
    linarith only [cubic]
  have amplitudePositive : 0 < scales.amplitude := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) amplitudeTwo
  filter_upwards [factory scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant
      boundaryConstant thresholdSmall referenceNonnegative boundaryOne orbit sectionTime,
    scales.eventually_cascade_physical_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_ge_atTop (max 1 (4 * constant))] with frequency memories foreignContinuity frequencyLarge
  intro count phase dipoleAngle requestedCap shapeRadius monitor prepared requestedPositive requestedSmall path index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let rate := constant * (1 + omega * epsilon)
  let centered := fun time => prepared.rawSourceCenteredState time index
  let foreign := prepared.physicalForeignSourceForcing index
  let drive := fun time => omega * centered time + foreign time
  let memory := fun time => constant * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * drive current
  have actual := memories count phase dipoleAngle prepared requestedPositive requestedSmall path index
  dsimp only at actual
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
  have ratioPositive : 0 < changed.ratio := zero_lt_one.trans_le ratioOne
  have frequencyOmega := changed.omega_ge_frequency frequencyPositive ratioOne (index.val + 1)
  have omegaOne : 1 ≤ omega := frequencyOne.trans frequencyOmega
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have omegaLarge : 4 * constant ≤ omega := ((le_max_right _ _).trans frequencyLarge).trans frequencyOmega
  have epsilonIdentity : omega * epsilon = 2 / (changed.amplitude * omega ^ 2) := by
    dsimp only [epsilon]
    rw [changed.radius_sq amplitudePositive frequencyPositive ratioPositive]
    dsimp only [omega]
    field_simp [(changed.length_pos (index.val + 1)).ne', amplitudePositive.ne', omegaPositive.ne']
    ring
  have epsilonSmall : omega * epsilon ≤ 1 := by
    rw [epsilonIdentity]
    have amplitudeNonnegative : 0 ≤ changed.amplitude := amplitudePositive.le
    have squareOne : 1 ≤ omega ^ 2 := one_le_pow₀ omegaOne
    have denominator : 2 ≤ changed.amplitude * omega ^ 2 :=
      amplitudeTwo.trans (le_mul_of_one_le_right amplitudeNonnegative squareOne)
    exact (div_le_one (by positivity : 0 < changed.amplitude * omega ^ 2)).mpr denominator
  have rateBound : rate ≤ 2 * constant := by
    have scaled := mul_le_mul_of_nonneg_left epsilonSmall (zero_le_one.trans constantOne)
    dsimp only [rate]
    linarith only [scaled]
  have rateOmega : rate ≤ omega / 2 := by linarith only [rateBound, omegaLarge]
  refine ⟨actual, rateBound, rateOmega, ?_⟩
  intro finish inside weight weightBound
  have weightPositive : 0 < weight := omegaPositive.trans_le weightBound
  have halfGap : rate ≤ weight / 2 := rateOmega.trans (div_le_div_of_nonneg_right weightBound (by norm_num))
  have gapPositive : 0 < weight - rate := by linarith only [halfGap, weightPositive]
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl inside.2
  have centerContinuous := (faithful_centered_state_continuous prepared path index).mono subset
  have foreignActual := foreignContinuity count phase dipoleAngle prepared path index
  have foreignContinuous := foreignActual.2.1.mono subset
  have memoryContinuous : ContinuousOn memory (Icc 0 finish) := actual.1.mono subset
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have centerIntegrable := (weightContinuous.continuousOn.mul centerContinuous).intervalIntegrable_of_Icc (μ := volume) inside.1
  have foreignIntegrable := (weightContinuous.continuousOn.mul foreignContinuous).intervalIntegrable_of_Icc (μ := volume) inside.1
  have memoryIntegrable := (weightContinuous.continuousOn.mul memoryContinuous).intervalIntegrable_of_Icc (μ := volume) inside.1
  have driveContinuous : ContinuousOn drive (Icc 0 finish) := (continuousOn_const.mul centerContinuous).add foreignContinuous
  have centeredNonnegative (time : ℝ) : 0 ≤ centered time :=
    div_nonneg (norm_nonneg _) (changed.length_pos _).le
  have driveNonnegative (time : ℝ) : 0 ≤ drive time :=
    add_nonneg (mul_nonneg omegaPositive.le (centeredNonnegative time)) (prepared.physicalForeignSourceForcing_nonneg index time)
  have convolution := EulerNonuniqueness.weighted_exponential_convolution_integral_le driveContinuous
    (sub_pos.mp gapPositive) inside.1 (fun time _ => driveNonnegative time)
  have scaled := mul_le_mul_of_nonneg_left convolution (zero_le_one.trans constantOne)
  have memoryIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * memory time) =
      constant * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * drive current) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    dsimp only [memory]
    ring
  have driveIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * drive time) =
      omega * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * centered time) +
        ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign time := by
    dsimp only [drive]
    simp_rw [mul_add, mul_left_comm (Real.exp _) omega]
    rw [intervalIntegral.integral_add (centerIntegrable.const_mul omega) foreignIntegrable,
      intervalIntegral.integral_const_mul]
  have driveIntegralNonnegative : 0 ≤ ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * drive time :=
    intervalIntegral.integral_nonneg inside.1 fun time _ => mul_nonneg (Real.exp_pos _).le (driveNonnegative time)
  have gain : constant / (weight - rate) ≤ 2 * constant / weight := by
    apply (div_le_div_iff₀ gapPositive weightPositive).mpr
    have scaledGap := mul_le_mul_of_nonneg_left halfGap (zero_le_one.trans constantOne)
    nlinarith only [scaledGap]
  have gainBound := mul_le_mul_of_nonneg_right gain driveIntegralNonnegative
  refine ⟨memoryIntegrable, centerIntegrable, foreignIntegrable, ?_⟩
  rw [memoryIdentity]
  apply scaled.trans
  have normalized := gainBound
  rw [driveIdentity] at normalized
  rw [driveIdentity]
  convert normalized using 1; ring

end EulerNonuniqueness.Paper

