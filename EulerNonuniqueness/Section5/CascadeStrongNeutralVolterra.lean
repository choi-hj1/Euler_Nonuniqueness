import EulerNonuniqueness.Section5.CascadeStrongNeutralOriginalHistory

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_strong_neutral_volterra
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ},
    0 < scaleRoot → 0 ≤ boundaryConstant → 0 < factor → factor ≤ 1 / 8 →
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    ∀ time ∈ Icc 0 finish,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
      (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / changed.length (index.val + 1) ≤
      (changed.length (index.val + 1) / (4 * changed.location (index.val + 1))) *
        ‖relativeNormalizedFirstMoment changed first second index time‖ +
      constant * (|diagonalDifference first time index - diagonalDifference second time index| / changed.length (index.val + 1) ^ 2 +
        |(referenceStraightenedShape first graph coordinate index time).1 - (referenceStraightenedShape second graph coordinate index time).1| +
        |(referenceStraightenedShape first graph coordinate index time).2 - (referenceStraightenedShape second graph coordinate index time).2| +
        ∫ current in (0 : ℝ)..time,
          |relativeCorrectedPaperPhaseVelocity changed (phaseCorrection 1 graph) (cascadePairedMotion prepared) index current|) := by
  obtain ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, history⟩ :=
    exists_uniform_cascade_strong_neutral_original_history graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [history scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative factorPositive
    factorSmall thresholdSmall referenceNonnegative] with frequency actual
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound small time inside
  obtain ⟨lift, _, _, integral, reconstruct⟩ :=
    actual prepared path index nonterminal finish finishNonnegative finishBound small
  have bound := reconstruct time inside
  dsimp only at bound ⊢
  rw [integral time inside] at bound
  have integralNorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := (0 : ℝ)) (b := time)
    (f := fun current => relativeCorrectedPaperPhaseVelocity {scales with frequency := frequency}
      (phaseCorrection 1 graph) (cascadePairedMotion prepared) index current) inside.1
  simp only [Real.norm_eq_abs] at integralNorm
  exact bound.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left (add_le_add_left integralNorm _) (zero_le_one.trans constantOne)) _)

end EulerNonuniqueness.Paper
