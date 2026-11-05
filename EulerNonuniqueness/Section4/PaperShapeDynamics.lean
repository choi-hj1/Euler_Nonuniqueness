import EulerNonuniqueness.Section4.PaperHalfDiagonalDynamics
import EulerNonuniqueness.Section4.PaperCoarseUpperBranch
import EulerNonuniqueness.Section4.ReferenceComputedShapeEquation

noncomputable section

open Set Filter EulerNonuniqueness.Section6
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem FinitePatchEvolution.centroid_paper_shape_hasDerivAt_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count) (inside : time ∈ Ioo 0 horizon)
    (small : |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4) :
    HasDerivAt (fun current => (unstableShape motion current index, stableShape motion current index))
      (referencePointShapeVelocity scales motion time index) time := by
  have upper := paper_shape_ratio_im_pos_of_small motion time index small
  have paper := pointShapeChart_eq_paper_shape_of_upper motion time index upper
  have coherentSmall : |(pointShapeChart (positiveHalfDiagonal motion time index)
      (negativeHalfDiagonal motion time index)).1| +
      |(pointShapeChart (positiveHalfDiagonal motion time index)
        (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4 := by rwa [paper]
  obtain ⟨positiveNonzero, negativeNonzero, _, ratioUpper⟩ :=
    pointShapeChart_reference_annulus (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) coherentSmall
  have normPositive : 0 < ‖positiveHalfDiagonal motion time index‖ := norm_pos_iff.mpr positiveNonzero
  have normOrder : ‖negativeHalfDiagonal motion time index‖ < ‖positiveHalfDiagonal motion time index‖ := by
    have bounded := (div_le_iff₀ normPositive).mp ratioUpper
    nlinarith only [bounded, normPositive]
  have differenceNonzero : positiveHalfDiagonal motion time index - negativeHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have equal := sub_eq_zero.mp zero
    rw [equal] at normOrder
    exact lt_irrefl _ normOrder
  have sumNonzero : positiveHalfDiagonal motion time index + negativeHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have equal : negativeHalfDiagonal motion time index = -positiveHalfDiagonal motion time index :=
      eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using zero)
    rw [equal, norm_neg] at normOrder
    exact lt_irrefl _ normOrder
  have noncollision := centrallySymmetricFourPoint_noncollision positiveNonzero negativeNonzero differenceNonzero sumNonzero
  have equation (patch : Fin 4) := evolution.patchCentroid_hasDerivAt_point_field_of_boundary_gaps
    horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch inside
  have actual := fourPointShapeChart_actual_forced_equation
    (trajectory := fun current patch => patchCentroid motion current index patch)
    (forcing := quadrupoleCentroidForcing scales motion time index) noncollision normOrder
    (pointShapeChart_leftHalfPlane_of_small positiveNonzero negativeNonzero coherentSmall)
    (fun patch => by simpa only [quadrupoleCentroidForcing, add_assoc] using equation patch)
  dsimp only at actual
  change HasDerivAt (fun current => pointShapeChart (positiveHalfDiagonal motion current index)
      (negativeHalfDiagonal motion current index))
    (shapeChartVelocity (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
      diagonalDifference motion time index)
      (pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)) +
      referencePointShapeForcing scales motion time index) time at actual
  rw [paper] at actual
  change HasDerivAt (fun current => pointShapeChart (positiveHalfDiagonal motion current index)
    (negativeHalfDiagonal motion current index)) (referencePointShapeVelocity scales motion time index) time at actual
  have positiveContinuous : ContinuousAt (fun current => positiveHalfDiagonal motion current index) time :=
    ((equation 0).continuousAt.sub (equation 1).continuousAt).div_const 2
  have negativeContinuous : ContinuousAt (fun current => negativeHalfDiagonal motion current index) time :=
    ((equation 2).continuousAt.sub (equation 3).continuousAt).div_const 2
  have imaginaryContinuous := Complex.continuous_im.continuousAt.comp (negativeContinuous.div positiveContinuous positiveNonzero)
  have near := imaginaryContinuous.eventually (eventually_gt_nhds upper)
  apply actual.congr_of_eventuallyEq
  filter_upwards [near] with current currentUpper
  exact (pointShapeChart_eq_paper_shape_of_upper motion current index currentUpper).symm

end EulerNonuniqueness.Paper
