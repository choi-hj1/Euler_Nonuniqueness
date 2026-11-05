import EulerNonuniqueness.Section4.InitialRegularizedShape
import EulerNonuniqueness.Section3.MovingCentroidGaugeJointCentroids

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingReferenceCoordinatesHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingReferenceCoordinatesC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def movingReferenceShapeCoordinates {count : ℕ} (scales : Scales)
    (state : MovingContourState (count * 4)) (index : Fin count) : ℝ × ℝ :=
  regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
    ((state.2.1 (finProdFinEquiv (index, 0)) - state.2.1 (finProdFinEquiv (index, 1))) / 2)
    ((state.2.1 (finProdFinEquiv (index, 2)) - state.2.1 (finProdFinEquiv (index, 3))) / 2)

theorem movingReferenceShapeCoordinates_continuous {count : ℕ} (scales : Scales) (index : Fin count) :
    Continuous (fun state : MovingContourState (count * 4) => movingReferenceShapeCoordinates scales state index) := by
  have centerContinuous (patch : Fin 4) : Continuous (fun state : MovingContourState (count * 4) =>
      state.2.1 (finProdFinEquiv (index, patch))) :=
    (continuous_apply (finProdFinEquiv (index, patch))).comp (continuous_fst.comp continuous_snd)
  have diagonals := (((centerContinuous 0).sub (centerContinuous 1)).div_const 2).prodMk
    (((centerContinuous 2).sub (centerContinuous 3)).div_const 2)
  have denominatorPositive : 0 < scales.length (index.val + 1) ^ 2 / 2 :=
    div_pos (sq_pos_of_pos (scales.length_pos _)) (by norm_num)
  unfold movingReferenceShapeCoordinates
  have actual := (regularizedShapeCoordinates_continuous denominatorPositive (by norm_num : (0 : ℝ) < 1 / 16)).comp diagonals
  simpa only [Function.comp_def] using actual

theorem movingReferenceShapeCoordinates_initial {count : ℕ} (scales : Scales)
    (phase unstable : Fin count → ℝ) (small : ∀ index, |unstable index| ≤ 1 / 2) (index : Fin count) :
    movingReferenceShapeCoordinates scales
      ((0 : ℝ), (fun label : Fin (count * 4) => initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
        (phase (finProdFinEquiv.symm label).1) (unstable (finProdFinEquiv.symm label).1)
        (finProdFinEquiv.symm label).2), fun _ : Fin (count * 4) => standardCircleBanach) index =
      (unstable index, 0) := by
  unfold movingReferenceShapeCoordinates
  simp only [Equiv.symm_apply_apply]
  have positive : (initialDiskCenter scales (index.val + 1) (phase index) (unstable index) 0 -
      initialDiskCenter scales (index.val + 1) (phase index) (unstable index) 1) / 2 =
      initialPositiveDiagonal scales (index.val + 1) (phase index) (unstable index) := by
    simp only [initialDiskCenter, Fin.reduceEq, if_true, if_false]
    ring
  have negative : (initialDiskCenter scales (index.val + 1) (phase index) (unstable index) 2 -
      initialDiskCenter scales (index.val + 1) (phase index) (unstable index) 3) / 2 =
      initialNegativeDiagonal scales (index.val + 1) (phase index) (unstable index) := by
    simp only [initialDiskCenter, Fin.reduceEq, if_true, if_false]
    ring
  rw [positive, negative]
  exact initialDiagonals_regularizedShape_eq scales _ _ _ (small index)

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

theorem patchCentroid_eq_curve_center
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) (patch : Fin 4) :
    patchCentroid trajectory.movingFamily.patchMotion time index patch =
      (trajectory.curve time).2.1 (finProdFinEquiv (index, patch)) := by
  rw [FiniteMovingPatchFamily.patchCentroid_eq]
  exact (trajectory.movingPatch_centroid_eq_center_of_initial_circles initialCircles inside _).trans
    (trajectory.center_eq_curve inside _)

theorem movingReferenceShapeCoordinates_eq_paper
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach) (scales : Scales)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count)
    (denominatorLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      ‖positiveHalfDiagonal trajectory.movingFamily.patchMotion time index‖ ^ 2)
    (imaginaryLower : (1 / 16 : ℝ) ≤
      (negativeHalfDiagonal trajectory.movingFamily.patchMotion time index /
        positiveHalfDiagonal trajectory.movingFamily.patchMotion time index).im) :
    movingReferenceShapeCoordinates scales (trajectory.curve time) index =
      (unstableShape trajectory.movingFamily.patchMotion time index,
        stableShape trajectory.movingFamily.patchMotion time index) := by
  unfold movingReferenceShapeCoordinates
  have positive : ((trajectory.curve time).2.1 (finProdFinEquiv (index, 0)) -
      (trajectory.curve time).2.1 (finProdFinEquiv (index, 1))) / 2 =
      positiveHalfDiagonal trajectory.movingFamily.patchMotion time index := by
    rw [positiveHalfDiagonal, trajectory.patchCentroid_eq_curve_center initialCircles inside index 0,
      trajectory.patchCentroid_eq_curve_center initialCircles inside index 1]
  have negative : ((trajectory.curve time).2.1 (finProdFinEquiv (index, 2)) -
      (trajectory.curve time).2.1 (finProdFinEquiv (index, 3))) / 2 =
      negativeHalfDiagonal trajectory.movingFamily.patchMotion time index := by
    rw [negativeHalfDiagonal, trajectory.patchCentroid_eq_curve_center initialCircles inside index 2,
      trajectory.patchCentroid_eq_curve_center initialCircles inside index 3]
  rw [positive, negative]
  exact regularizedShapeCoordinates_eq_paper _ _ _ denominatorLower imaginaryLower

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
