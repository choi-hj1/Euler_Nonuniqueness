import EulerNonuniqueness.Section4.PaperShapeForcingContinuity
import EulerNonuniqueness.Section6.ShapeVelocityContinuity

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

theorem exists_uniform_paper_shape_velocity_continuity_radius :
    ∃ radius > (0 : ℝ), ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ},
    FinitePatchEvolution scales motion horizon → 0 < horizon →
    0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
    (∀ index : Fin count, 0 < scales.radius (index.val + 1)) →
    (∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound) →
    (∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0)) →
    ∀ index : Fin count,
    (∀ time ∈ Icc 0 horizon, FourPointNoncollision (fun patch => patchCentroid motion time index patch)) →
    (∀ time ∈ Icc 0 horizon, diagonalDifference motion time index ≠ 0) →
    (∀ time ∈ Icc 0 horizon,
      |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4) →
    (∀ time ∈ Icc 0 horizon,
      ‖(unstableShape motion time index, stableShape motion time index)‖ < radius) →
    ContinuousOn (fun time => referencePointShapeVelocity scales motion time index) (Icc 0 horizon) := by
  obtain ⟨radius, radiusPositive, normalized⟩ := exists_uniform_shapeChartVelocity_continuousOn_radius
  refine ⟨radius, radiusPositive, ?_⟩
  intro count scales motion horizon evolution horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index noncollision differenceNonzero small size
  have centroids (patch : Fin 4) := (evolution.patchCentroid_closed_derivative_of_boundary_gaps
    horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch).1
  have positive : ContinuousOn (fun time => positiveHalfDiagonal motion time index) (Icc 0 horizon) := by
    unfold positiveHalfDiagonal
    exact ((centroids 0).sub (centroids 1)).div_const 2
  have negative : ContinuousOn (fun time => negativeHalfDiagonal motion time index) (Icc 0 horizon) := by
    unfold negativeHalfDiagonal
    exact ((centroids 2).sub (centroids 3)).div_const 2
  have difference : ContinuousOn (fun time => diagonalDifference motion time index) (Icc 0 horizon) :=
    (positive.norm.pow 2).sub (negative.norm.pow 2)
  have rate : ContinuousOn (fun time => scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
      diagonalDifference motion time index) (Icc 0 horizon) :=
    continuousOn_const.div difference differenceNonzero
  have shape := evolution.paper_shape_continuousOn_of_boundary_gaps horizonPositive amplitudePositive
    frequencyPositive ratioPositive radiusPositive control separated index small
  have forcing := evolution.referencePointShapeForcing_continuousOn_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index noncollision small
  exact (normalized (Icc 0 horizon)
    (fun time => scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
      diagonalDifference motion time index)
    (fun time => (unstableShape motion time index, stableShape motion time index)) rate shape size).add forcing

end EulerNonuniqueness.Paper
