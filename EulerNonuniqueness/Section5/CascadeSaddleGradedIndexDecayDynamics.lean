import EulerNonuniqueness.Section5.CascadeSaddleGradedIndexDecayBudget
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_saddle_graded_index_decay_dynamics :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {scaleRoot boundaryConstant factor threshold coarseConstant : ℝ},
      0 < scaleRoot → 0 ≤ boundaryConstant → 0 < factor → factor ≤ 1 / 8 →
      threshold ≤ thresholdMax → 0 ≤ coarseConstant →
      ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold coarseConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared,
      ∀ index : Fin count, index.val + 1 < count → ∀ time ∈ Ioo 0 path.stop,
      (∀ current ∈ Icc 0 time,
        |unstableShape prepared.trajectory.movingFamily.patchMotion current index| +
          |stableShape prepared.trajectory.movingFamily.patchMotion current index| ≤ radius) →
      HasDerivAt (fun current => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index current -
          referenceStraightenedShape prepared.reference graph coordinate index current)
        (relativeStraightenedSaddleVelocity {scales with frequency := frequency}
          (cascadePairedMotion prepared) graph coordinate index time) time ∧
      let changed : Scales := {scales with frequency := frequency}
      let first := referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time
      let second := referenceStraightenedShape prepared.reference graph coordinate index time
      let difference := |first.1 - second.1| + |first.2 - second.2|
      let dilationDifference := |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index -
        diagonalDifference prepared.reference time index| / changed.length (index.val + 1) ^ 2
      let referenceSize := chartConstant * coarseConstant *
        ((changed.strain + changed.strain ^ 2) / changed.omega (index.val + 1) +
          (changed.omega (index.val + 1))⁻¹ ^ 5)
      ‖relativeStraightenedSaddlePointRemainder changed (cascadePairedMotion prepared) graph coordinate index time‖ ≤
        constant * |changed.omega (index.val + 1)| *
          ((referenceSize + dilationDifference + |first.2 - second.2|) * difference + referenceSize * dilationDifference) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, pointConstant, pointNonnegative, errorConstant, errorOne,
    baseRadius, basePositive, baseQuarter, compatible, dynamics⟩ :=
    exists_uniform_cascade_saddle_point_remainder
  obtain ⟨baseThreshold, thresholdPositive, chartConstant, chartOne, decayBudget⟩ :=
    exists_uniform_cascade_saddle_graded_index_decay_budget graphAnalytic.contDiffAt coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  let thresholdMax := min baseThreshold (1 / 8)
  let radius := baseRadius / 2
  let constant := 1 + 12 * Real.sqrt 2 + 4 * pointConstant + 4 * errorConstant
  have constantOne : 1 ≤ constant := by
    have rootNonnegative := Real.sqrt_nonneg (2 : ℝ)
    dsimp only [constant]
    linarith
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusBase : radius < baseRadius := by dsimp only [radius]; linarith
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, constant, constantOne,
    thresholdMax, lt_min thresholdPositive (by norm_num), min_le_right _ _, radius, radiusPositive,
    radiusBase.le.trans baseQuarter, compatible, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold coarseConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall coarseNonnegative
  have thresholdEighth : threshold ≤ 1 / 8 := thresholdSmall.trans (min_le_right _ _)
  have thresholdBase : threshold ≤ baseThreshold := thresholdSmall.trans (min_le_left _ _)
  filter_upwards [dynamics scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      factorPositive factorSmall thresholdEighth coarseNonnegative,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive coarseNonnegative basePositive]
    with frequency actual referenceSmall
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal time inside small
  have pairedSmall : ∀ side, ∀ current ∈ Icc 0 time,
      |unstableShape (cascadePairedMotion prepared side) current index| +
        |stableShape (cascadePairedMotion prepared side) current index| < baseRadius := by
    intro side current member
    fin_cases side
    · exact (small current member).trans_lt radiusBase
    · have sharp := referenceSmall prepared current
        (show current ∈ Icc (0 : ℝ) 1 from ⟨member.1, member.2.trans (inside.2.le.trans path.stopBound)⟩) index
      change |unstableShape prepared.reference current index| + |stableShape prepared.reference current index| < baseRadius
      linarith [abs_nonneg (diagonalDifference prepared.reference current index /
        ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 - 1)]
  obtain ⟨derivative, remainder⟩ := actual prepared path index nonterminal time inside pairedSmall
  refine ⟨derivative, ?_⟩
  exact remainder.trans (decayBudget prepared path thresholdBase time ⟨inside.1.le, inside.2.le⟩ index
    pointConstant errorConstant pointNonnegative (zero_le_one.trans errorOne))

end EulerNonuniqueness.Paper
