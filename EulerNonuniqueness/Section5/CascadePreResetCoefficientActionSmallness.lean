import EulerNonuniqueness.Section5.CascadePreResetCoefficientAction
import EulerNonuniqueness.Section1.UniformSeedActionSmallness

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_preReset_coefficient_action_smallness :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ momentConstant ≥ (0 : ℝ), ∃ dilationConstant ≥ (0 : ℝ),
    ∀ graph coordinate : ℝ → ℝ, ∀ chartConstant : ℝ, 0 ≤ chartConstant →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {scaleRoot boundaryConstant threshold referenceConstant : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ {forcingConstant exponent tolerance : ℝ},
    0 ≤ forcingConstant → 0 < exponent → 0 < tolerance →
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
    let seed := changed.seed (index.val + 1) ^ exponent
    let forcingBound := forcingConstant * omega * seed
    ContinuousOn stable (Icc 0 finish) →
    (∀ time ∈ Icc 0 finish, |stable time| ≤ seed) →
    (∀ time ∈ Icc 0 finish, momentForcing time ≤ forcingBound) →
    (∀ time ∈ Icc 0 finish, dilationForcing time ≤ forcingBound) →
    ContinuousOn (fun time => referenceSize + dilation time + |stable time|) (Icc 0 finish) ∧
    IntervalIntegrable (fun time => referenceSize + dilation time + |stable time|) volume 0 finish ∧
    omega * (∫ time in (0 : ℝ)..finish, referenceSize + dilation time + |stable time|) < tolerance := by
  obtain ⟨rawCap, capPositive, factory⟩ := exists_uniform_actual_preReset_coefficient_action
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨momentConstant, momentNonnegative, dilationConstant, dilationNonnegative, estimates⟩ :=
    factory factorPositive factorSmall
  refine ⟨momentConstant, momentNonnegative, dilationConstant, dilationNonnegative, ?_⟩
  intro graph coordinate chartConstant chartNonnegative scales amplitudePositive ratioBound alphaPositive orbit sectionTime
    scaleRoot boundaryConstant threshold referenceConstant rootOne boundaryOne thresholdSmall referenceNonnegative
    forcingConstant exponent tolerance forcingNonnegative exponentPositive tolerancePositive
  filter_upwards [estimates graph coordinate chartConstant chartNonnegative scales amplitudePositive ratioBound alphaPositive
      orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative,
    scales.eventually_uniform_seed_action_budget_small ratioBound alphaPositive
      (mul_nonneg chartNonnegative referenceNonnegative) forcingNonnegative exponentPositive tolerancePositive,
    eventually_gt_atTop (0 : ℝ)] with frequency actualEstimate scalarEstimate frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
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
  let seed := changed.seed (index.val + 1) ^ exponent
  let forcingBound := forcingConstant * omega * seed
  intro stableContinuous stableSmall momentBound dilationBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have seedNonnegative : 0 ≤ seed := Real.rpow_nonneg
    (changed.seed_pos frequencyPositive ratioPositive _).le exponent
  have forcingBoundNonnegative : 0 ≤ forcingBound := by
    dsimp only [forcingBound]
    positivity
  have actual := actualEstimate count phase dipoleAngle prepared path index nonterminal finish
    finishNonnegative finishBound radialSmall forcingBound seed forcingBoundNonnegative seedNonnegative
    stableContinuous stableSmall momentBound dilationBound
  have scalar := scalarEstimate (index.val + 1) finish
    (show finish ∈ Icc (0 : ℝ) 1 from ⟨finishNonnegative, finishBound.trans path.stopBound⟩)
  exact ⟨actual.2.1, actual.2.2.1, actual.2.2.2.trans_lt scalar⟩

end EulerNonuniqueness.Paper

