import EulerNonuniqueness.Section5.CascadeRelativeNeutralHistory

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

def quadrupoleDiagonalVelocity
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) (time : ℝ) : ℝ :=
  2 * @inner ℝ ℂ _ (positiveHalfDiagonal trajectory.movingFamily.patchMotion time index)
    (((trajectory.velocity time).2.1 (finProdFinEquiv (index, 0)) -
      (trajectory.velocity time).2.1 (finProdFinEquiv (index, 1))) / 2) -
  2 * @inner ℝ ℂ _ (negativeHalfDiagonal trajectory.movingFamily.patchMotion time index)
    (((trajectory.velocity time).2.1 (finProdFinEquiv (index, 2)) -
      (trajectory.velocity time).2.1 (finProdFinEquiv (index, 3))) / 2)

theorem quadrupoleDiagonalVelocity_continuous
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) :
    Continuous (trajectory.quadrupoleDiagonalVelocity index) := by
  have velocity (patch : Fin 4) : Continuous (fun time =>
      (trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) :=
    (continuous_apply _).comp (continuous_fst.comp (continuous_snd.comp trajectory.velocity_continuous))
  have positive := ((trajectory.movingFamily.patchCentroid_continuous index 0).sub
    (trajectory.movingFamily.patchCentroid_continuous index 1)).div_const 2
  have negative := ((trajectory.movingFamily.patchCentroid_continuous index 2).sub
    (trajectory.movingFamily.patchCentroid_continuous index 3)).div_const 2
  exact (continuous_const.mul (positive.inner ((velocity 0).sub (velocity 1) |>.div_const 2))).sub
    (continuous_const.mul (negative.inner ((velocity 2).sub (velocity 3) |>.div_const 2)))

theorem diagonalDifference_hasDerivAt_quadrupoleDiagonalVelocity
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    (index : Fin count) {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) :
    HasDerivAt (fun current => diagonalDifference trajectory.movingFamily.patchMotion current index)
      (trajectory.quadrupoleDiagonalVelocity index time) time := by
  have point (patch : Fin 4) : HasDerivAt
      (fun current => patchCentroid trajectory.movingFamily.patchMotion current index patch)
      ((trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))) time := by
    apply (trajectory.center_hasDerivAt (finProdFinEquiv (index, patch)) time).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
    exact (trajectory.cascadeCenters_eq_patchCentroid initialCircles member index patch).symm
  have positive := ((point 0).sub (point 1)).div_const 2
  have negative := ((point 2).sub (point 3)).div_const 2
  exact positive.norm_sq.sub negative.norm_sq

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
