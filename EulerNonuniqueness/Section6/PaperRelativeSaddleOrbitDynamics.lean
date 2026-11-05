import EulerNonuniqueness.Section6.PointNormalFormOrbitWitness

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem exists_uniform_paper_relative_saddle_orbit_dynamics :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∀ {count : ℕ} {scales : Scales} {horizon time : ℝ} (motion : Fin 2 → PatchMotion count),
      ∀ (evolution : ∀ side, FinitePatchEvolution scales (motion side) horizon), 0 < horizon →
      0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
      (∀ source : Fin count, 0 < scales.radius (source.val + 1)) →
      (∀ side, ∀ current ∈ Icc 0 horizon, ∀ source patch,
        ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle scales (motion side) current source patch error) →
      (∀ side, ∀ current ∈ Icc 0 horizon, ∀ (source other : Fin count) (patch otherPatch : Fin 4),
        (other, otherPatch) ≠ (source, patch) →
        8 * scales.radius (source.val + 1) + 8 * scales.radius (other.val + 1) <
          dist ((motion side).boundary current source patch 0) ((motion side).boundary current other otherPatch 0)) →
      ∀ index : Fin count, time ∈ Ioo 0 horizon →
      (∀ side, |unstableShape (motion side) time index| + |stableShape (motion side) time index| < radius) →
      let frequency := fun side => scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
        diagonalDifference (motion side) time index
      let chart := fun side => referenceStraightenedShape (motion side) graph coordinate index time
      let error := fun side => localNormalFormError 1 graph coordinate
        (unstableShape (motion side) time index, stableShape (motion side) time index)
      let forcing := fun side => referenceStraightenedForcing scales (motion side) graph coordinate index time
      HasDerivAt (fun current => referenceStraightenedShape (motion 0) graph coordinate index current -
          referenceStraightenedShape (motion 1) graph coordinate index current)
        ((2 * Real.sqrt 2 * scales.omega (index.val + 1) * ((chart 0).1 - (chart 1).1),
            -(2 * Real.sqrt 2 * scales.omega (index.val + 1)) * ((chart 0).2 - (chart 1).2)) +
          (2 * Real.sqrt 2 * ((frequency 0 - scales.omega (index.val + 1)) * (chart 0).1 -
              (frequency 1 - scales.omega (index.val + 1)) * (chart 1).1),
            -(2 * Real.sqrt 2) * ((frequency 0 - scales.omega (index.val + 1)) * (chart 0).2 -
              (frequency 1 - scales.omega (index.val + 1)) * (chart 1).2)) +
          frequency 0 • (error 0 - error 1) + (frequency 0 - frequency 1) • error 1 +
            (forcing 0 - forcing 1)) time ∧
      ‖error 0 - error 1‖ ≤ constant * (|(chart 0).1 - (chart 1).1| + |(chart 0).2 - (chart 1).2|) *
        (|(chart 0).2 - (chart 1).2| + |(chart 1).1| + |(chart 1).2|) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, constant, constantNonnegative, radius, radiusPositive, bound, orbitCompatible⟩ :=
    exists_uniform_pointNormalForm_memory_orbit_compatible
  have graphDifferentiable : ∀ᶠ unstable in nhds (0 : ℝ), DifferentiableAt ℝ graph unstable :=
    ((graphAnalytic.contDiffAt (n := 1)).eventually (by norm_num)).mono
      (fun _ smooth => smooth.differentiableAt (by norm_num))
  have coordinateOnce : ContDiffAt ℝ 1 coordinate 0 := coordinateSmooth.of_le (by norm_num)
  have coordinateDifferentiable : ∀ᶠ unstable in nhds (0 : ℝ), DifferentiableAt ℝ coordinate unstable :=
    (coordinateOnce.eventually (by norm_num)).mono (fun _ smooth => smooth.differentiableAt (by norm_num))
  obtain ⟨derivativeRadius, derivativePositive, derivativeInside⟩ :=
    Metric.mem_nhds_iff.mp (graphDifferentiable.and coordinateDifferentiable)
  let actualRadius := min radius (min derivativeRadius (1 / 4))
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, constant, constantNonnegative, actualRadius,
    by dsimp only [actualRadius]; positivity,
    (min_le_right _ _).trans (min_le_right _ _), orbitCompatible, ?_⟩
  intro count scales horizon time motion evolution horizonPositive amplitudePositive frequencyPositive ratioPositive
    radii control separated index inside small
  dsimp only
  let frequency := fun side => scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
    diagonalDifference (motion side) time index
  let chart := fun side => referenceStraightenedShape (motion side) graph coordinate index time
  let error := fun side => localNormalFormError 1 graph coordinate
    (unstableShape (motion side) time index, stableShape (motion side) time index)
  let forcing := fun side => referenceStraightenedForcing scales (motion side) graph coordinate index time
  have equations (side : Fin 2) : HasDerivAt (referenceStraightenedShape (motion side) graph coordinate index)
      ((2 * Real.sqrt 2 * frequency side * (chart side).1,
          -(2 * Real.sqrt 2 * frequency side) * (chart side).2) +
        frequency side • error side + forcing side) time := by
    have chartSmall : |unstableShape (motion side) time index| + |stableShape (motion side) time index| ≤ 1 / 4 :=
      (small side).le.trans ((min_le_right _ _).trans (min_le_right _ _))
    have derivatives := derivativeInside
      (show unstableShape (motion side) time index ∈ Metric.ball (0 : ℝ) derivativeRadius by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
        exact (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg _)) (small side)).trans_le
          ((min_le_right _ _).trans (min_le_left _ _)))
    have equation := (evolution side).centroid_paper_shape_hasDerivAt_of_boundary_gaps horizonPositive
      amplitudePositive frequencyPositive ratioPositive radii (control side) (separated side) index inside chartSmall
    change HasDerivAt
      (fun current => (unstableShape (motion side) current index, stableShape (motion side) current index))
      (shapeChartVelocity (frequency side) (unstableShape (motion side) time index,
        stableShape (motion side) time index) + referencePointShapeForcing scales (motion side) time index) time at equation
    have actual := localNormalFormChart_forced_equation equation derivatives.1 derivatives.2
    rw [localNormalFormError_frequency_smul (frequency side) graph coordinate] at actual
    convert actual using 1 <;>
      dsimp only [referenceStraightenedShape, referenceStraightenedForcing, frequency, chart, error, forcing,
        Prod.add_def, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ext <;> ring
  constructor
  · have actual := (equations 0).sub (equations 1)
    convert actual using 1 <;>
      dsimp only [frequency, chart, error, forcing, Prod.add_def, Prod.sub_def,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ext <;> ring
  · have actual := bound 1
      (unstableShape (motion 0) time index, stableShape (motion 0) time index)
      (unstableShape (motion 1) time index, stableShape (motion 1) time index)
      ((small 0).trans_le (min_le_left _ _)) ((small 1).trans_le (min_le_left _ _))
    simpa only [abs_one, mul_one, referenceStraightenedShape] using actual

end EulerNonuniqueness.Paper
