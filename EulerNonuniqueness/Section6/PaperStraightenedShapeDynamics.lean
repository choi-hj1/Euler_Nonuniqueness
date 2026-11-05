import EulerNonuniqueness.Section6.NormalFormChart
import EulerNonuniqueness.Section6.ShapeVelocityContinuity
import EulerNonuniqueness.Section4.PaperShapeDynamics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem localNormalFormError_frequency_smul (frequency : ℝ) (graph coordinate : ℝ → ℝ) (point : ℝ × ℝ) :
    localNormalFormError frequency graph coordinate point = frequency • localNormalFormError 1 graph coordinate point := by
  rw [localNormalFormError, shapeChartVelocity_frequency_smul]
  ext <;> simp only [localNormalFormError, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def referenceStraightenedShape {count : ℕ} (motion : PatchMotion count) (graph coordinate : ℝ → ℝ)
    (index : Fin count) (time : ℝ) : ℝ × ℝ :=
  localNormalFormChart graph coordinate (unstableShape motion time index, stableShape motion time index)

def referenceStraightenedForcing {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (graph coordinate : ℝ → ℝ) (index : Fin count) (time : ℝ) : ℝ × ℝ :=
  (deriv coordinate (unstableShape motion time index) * (referencePointShapeForcing scales motion time index).1,
    (referencePointShapeForcing scales motion time index).2 -
      deriv graph (unstableShape motion time index) * (referencePointShapeForcing scales motion time index).1)

set_option maxHeartbeats 2000000

theorem exists_uniform_paper_straightened_shape_dynamics :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ},
      ∀ (evolution : FinitePatchEvolution scales motion horizon), 0 < horizon →
      0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
      (∀ source : Fin count, 0 < scales.radius (source.val + 1)) →
      (∀ current ∈ Icc 0 horizon, ∀ source patch, ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current source patch error) →
      (∀ current ∈ Icc 0 horizon, ∀ (source other : Fin count) (patch otherPatch : Fin 4),
        (other, otherPatch) ≠ (source, patch) →
        8 * scales.radius (source.val + 1) + 8 * scales.radius (other.val + 1) <
          dist (motion.boundary current source patch 0) (motion.boundary current other otherPatch 0)) →
      ∀ index : Fin count, time ∈ Ioo 0 horizon →
      |unstableShape motion time index| + |stableShape motion time index| < radius →
      let frequency := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 / diagonalDifference motion time index
      let point := referenceStraightenedShape motion graph coordinate index time
      let error := localNormalFormError frequency graph coordinate (unstableShape motion time index, stableShape motion time index)
      HasDerivAt (referenceStraightenedShape motion graph coordinate index)
        ((2 * Real.sqrt 2 * frequency * point.1, -(2 * Real.sqrt 2 * frequency) * point.2) +
          error + referenceStraightenedForcing scales motion graph coordinate index time) time ∧
      |error.1| + |error.2| ≤ constant * |frequency| * |point.2| * (|point.1| + |point.2|) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, constant, constantNonnegative, radius, radiusPositive, bound⟩ :=
      localNormalForm_quadratic_stable_remainder_exists 1 (by norm_num)
  have graphDifferentiable : ∀ᶠ unstable in nhds (0 : ℝ), DifferentiableAt ℝ graph unstable :=
    ((graphAnalytic.contDiffAt (n := 1)).eventually (by norm_num)).mono (fun _ smooth => smooth.differentiableAt (by norm_num))
  have coordinateOnce : ContDiffAt ℝ 1 coordinate 0 := coordinateSmooth.of_le (by norm_num)
  have coordinateDifferentiable : ∀ᶠ unstable in nhds (0 : ℝ), DifferentiableAt ℝ coordinate unstable :=
    (coordinateOnce.eventually (by norm_num)).mono (fun _ smooth => smooth.differentiableAt (by norm_num))
  obtain ⟨derivativeRadius, derivativePositive, derivativeInside⟩ := Metric.mem_nhds_iff.mp (graphDifferentiable.and coordinateDifferentiable)
  let actualRadius := min radius (min derivativeRadius (1 / 4))
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, constant, constantNonnegative, actualRadius, by dsimp only [actualRadius]; positivity,
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro count scales motion horizon time evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radii control separated index inside small
  dsimp only
  have chartSmall : |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4 :=
    small.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have derivatives := derivativeInside (show unstableShape motion time index ∈ Metric.ball (0 : ℝ) derivativeRadius by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg _)) small).trans_le
      ((min_le_right _ _).trans (min_le_left _ _)))
  have equation := evolution.centroid_paper_shape_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radii control separated index inside chartSmall
  change HasDerivAt (fun current => (unstableShape motion current index, stableShape motion current index))
    (shapeChartVelocity (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 / diagonalDifference motion time index)
      (unstableShape motion time index, stableShape motion time index) + referencePointShapeForcing scales motion time index) time at equation
  have actual := localNormalFormChart_forced_equation equation derivatives.1 derivatives.2
  constructor
  · convert actual using 1 <;>
      dsimp only [referenceStraightenedShape, referenceStraightenedForcing, Prod.add_def] <;> ext <;> ring
  · rw [localNormalFormError_frequency_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul]
    have estimate := mul_le_mul_of_nonneg_left (bound _ _ (small.trans_le (min_le_left _ _)))
      (abs_nonneg (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 / diagonalDifference motion time index))
    convert estimate using 1 <;> dsimp only [referenceStraightenedShape, localNormalFormChart] <;> ring

end EulerNonuniqueness.Paper
