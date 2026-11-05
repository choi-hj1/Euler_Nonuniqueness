import EulerNonuniqueness.Section5.CascadePairedSaddleAdmissibility
import EulerNonuniqueness.Section5.CascadeRelativeChartInitial
import EulerNonuniqueness.Section6.PaperRelativeSaddleOrbitDynamics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def relativeStraightenedSaddleVelocity {count : ℕ} (scales : Scales) (motion : Fin 2 → PatchMotion count)
    (graph coordinate : ℝ → ℝ) (index : Fin count) (time : ℝ) : ℝ × ℝ :=
  let frequency := fun side => scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
    diagonalDifference (motion side) time index
  let chart := fun side => referenceStraightenedShape (motion side) graph coordinate index time
  let error := fun side => localNormalFormError 1 graph coordinate
    (unstableShape (motion side) time index, stableShape (motion side) time index)
  let forcing := fun side => referenceStraightenedForcing scales (motion side) graph coordinate index time
  (2 * Real.sqrt 2 * scales.omega (index.val + 1) * ((chart 0).1 - (chart 1).1),
      -(2 * Real.sqrt 2 * scales.omega (index.val + 1)) * ((chart 0).2 - (chart 1).2)) +
    (2 * Real.sqrt 2 * ((frequency 0 - scales.omega (index.val + 1)) * (chart 0).1 -
        (frequency 1 - scales.omega (index.val + 1)) * (chart 1).1),
      -(2 * Real.sqrt 2) * ((frequency 0 - scales.omega (index.val + 1)) * (chart 0).2 -
        (frequency 1 - scales.omega (index.val + 1)) * (chart 1).2)) +
    frequency 0 • (error 0 - error 1) + (frequency 0 - frequency 1) • error 1 + (forcing 0 - forcing 1)

theorem exists_uniform_cascade_coherent_saddle_dynamics :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ},
      0 < scaleRoot → 0 ≤ boundaryConstant → 0 < factor → factor ≤ 1 →
      threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared,
      (∀ index : Fin count, index.val + 1 < count →
        referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index 0 -
          referenceStraightenedShape prepared.reference graph coordinate index 0 = 0) ∧
      ∀ index : Fin count, ∀ time ∈ Ioo 0 path.stop,
      (∀ side, |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < radius) →
      HasDerivAt (fun current => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index current -
          referenceStraightenedShape prepared.reference graph coordinate index current)
        (relativeStraightenedSaddleVelocity {scales with frequency := frequency}
          (cascadePairedMotion prepared) graph coordinate index time) time ∧
      ‖localNormalFormError 1 graph coordinate
          (unstableShape prepared.trajectory.movingFamily.patchMotion time index,
            stableShape prepared.trajectory.movingFamily.patchMotion time index) -
        localNormalFormError 1 graph coordinate
          (unstableShape prepared.reference time index, stableShape prepared.reference time index)‖ ≤
        constant *
          (|(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).1 -
              (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
            |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).2 -
              (referenceStraightenedShape prepared.reference graph coordinate index time).2|) *
          (|(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).2 -
              (referenceStraightenedShape prepared.reference graph coordinate index time).2| +
            |(referenceStraightenedShape prepared.reference graph coordinate index time).1| +
            |(referenceStraightenedShape prepared.reference graph coordinate index time).2|) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, constant, constantNonnegative, radius, radiusPositive, radiusSmall, compatible, dynamics⟩ :=
    exists_uniform_paper_relative_saddle_orbit_dynamics
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, constant, constantNonnegative, radius, radiusPositive, radiusSmall, compatible, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant factor threshold referenceConstant
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_cascade_paired_saddle_admissible amplitudePositive ratioBound alphaPositive rootPositive
      boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative]
    with frequency frequencyPositive admissible
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path
  have actual := admissible prepared path
  refine ⟨fun index nonterminal => prepared.nonterminal_initial_straightened_difference graph coordinate index nonterminal, ?_⟩
  intro index time inside small
  have derivative := dynamics (cascadePairedMotion prepared) actual.1 path.stopPositive amplitudePositive
    frequencyPositive (by dsimp; linarith) actual.2.1 actual.2.2.1 actual.2.2.2 index inside small
  simpa only [relativeStraightenedSaddleVelocity, cascadePairedMotion, Fin.cases_zero, Fin.cases_succ] using derivative

end EulerNonuniqueness.Paper
