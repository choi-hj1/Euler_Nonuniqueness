import EulerNonuniqueness.Section4.MovingReferenceShootingCoordinates

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

def movingReferenceRadialObservable {count : ℕ} (scales : Scales)
    (state : MovingContourState (count * 4)) (index : Fin count) : ℝ :=
  (movingReferenceShapeCoordinates scales state index).1 + (movingReferenceShapeCoordinates scales state index).2

def movingReferenceRatioImaginary {count : ℕ} (scales : Scales)
    (state : MovingContourState (count * 4)) (index : Fin count) : ℝ :=
  (regularizedDiagonalRatio (scales.length (index.val + 1) ^ 2 / 2)
    ((state.2.1 (finProdFinEquiv (index, 0)) - state.2.1 (finProdFinEquiv (index, 1))) / 2)
    ((state.2.1 (finProdFinEquiv (index, 2)) - state.2.1 (finProdFinEquiv (index, 3))) / 2)).im

theorem movingReferenceRadialObservable_continuous {count : ℕ} (scales : Scales) (index : Fin count) :
    Continuous (fun state : MovingContourState (count * 4) => movingReferenceRadialObservable scales state index) :=
  (movingReferenceShapeCoordinates_continuous scales index).fst.add
    (movingReferenceShapeCoordinates_continuous scales index).snd

theorem movingReferenceRatioImaginary_continuous {count : ℕ} (scales : Scales) (index : Fin count) :
    Continuous (fun state : MovingContourState (count * 4) => movingReferenceRatioImaginary scales state index) := by
  have centerContinuous (patch : Fin 4) : Continuous (fun state : MovingContourState (count * 4) =>
      state.2.1 (finProdFinEquiv (index, patch))) :=
    (continuous_apply (finProdFinEquiv (index, patch))).comp (continuous_fst.comp continuous_snd)
  have diagonals := (((centerContinuous 0).sub (centerContinuous 1)).div_const 2).prodMk
    (((centerContinuous 2).sub (centerContinuous 3)).div_const 2)
  have positive : 0 < scales.length (index.val + 1) ^ 2 / 2 :=
    div_pos (sq_pos_of_pos (scales.length_pos _)) (by norm_num)
  exact Complex.continuous_im.comp ((regularizedDiagonalRatio_continuous positive).comp diagonals)

theorem movingReferenceRadialObservable_initial {count : ℕ} (scales : Scales)
    (phase unstable : Fin count → ℝ) (small : ∀ index, |unstable index| ≤ 1 / 2) (index : Fin count) :
    movingReferenceRadialObservable scales
      ((0 : ℝ), (fun label : Fin (count * 4) => initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
        (phase (finProdFinEquiv.symm label).1) (unstable (finProdFinEquiv.symm label).1)
        (finProdFinEquiv.symm label).2), fun _ : Fin (count * 4) => standardCircleBanach) index = unstable index := by
  simp only [movingReferenceRadialObservable, movingReferenceShapeCoordinates_initial scales phase unstable small index, add_zero]

theorem movingReferenceRatioImaginary_initial {count : ℕ} (scales : Scales)
    (phase unstable : Fin count → ℝ) (small : ∀ index, |unstable index| ≤ 1 / 2) (index : Fin count) :
    1 / 8 ≤ movingReferenceRatioImaginary scales
      ((0 : ℝ), (fun label : Fin (count * 4) => initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
        (phase (finProdFinEquiv.symm label).1) (unstable (finProdFinEquiv.symm label).1)
        (finProdFinEquiv.symm label).2), fun _ : Fin (count * 4) => standardCircleBanach) index := by
  unfold movingReferenceRatioImaginary
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
  have lower := (initialDiagonals_separation_bounds scales (index.val + 1) (phase index) (unstable index) (small index)).1
  have floor : scales.length (index.val + 1) ^ 2 / 2 ≤
      ‖initialPositiveDiagonal scales (index.val + 1) (phase index) (unstable index)‖ ^ 2 := by
    nlinarith [scales.length_pos (index.val + 1)]
  rw [regularizedDiagonalRatio_eq_of_lower_bound floor]
  exact initialDiagonals_ratio_im_lower scales _ _ _ (small index)

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

theorem movingReferenceMechanicalObservables_eq_paper
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach) (scales : Scales)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference trajectory.movingFamily.patchMotion time index) :
    movingReferenceRadialObservable scales (trajectory.curve time) index =
      radialShape trajectory.movingFamily.patchMotion time index ∧
    movingReferenceRatioImaginary scales (trajectory.curve time) index =
      (negativeHalfDiagonal trajectory.movingFamily.patchMotion time index /
        positiveHalfDiagonal trajectory.movingFamily.patchMotion time index).im := by
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
  have floor : scales.length (index.val + 1) ^ 2 / 2 ≤
      ‖positiveHalfDiagonal trajectory.movingFamily.patchMotion time index‖ ^ 2 := by
    dsimp only [diagonalDifference] at differenceLower
    nlinarith [sq_nonneg ‖negativeHalfDiagonal trajectory.movingFamily.patchMotion time index‖]
  constructor
  · unfold movingReferenceRadialObservable movingReferenceShapeCoordinates
    rw [positive, negative]
    dsimp only [regularizedShapeCoordinates]
    rw [max_eq_right floor]
    dsimp only [radialShape]
    ring
  · unfold movingReferenceRatioImaginary
    rw [positive, negative, regularizedDiagonalRatio_eq_of_lower_bound floor]

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
