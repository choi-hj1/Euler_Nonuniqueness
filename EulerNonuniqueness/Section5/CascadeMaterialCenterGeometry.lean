import EulerNonuniqueness.Section5.CascadeBlockExtentCentroids
import EulerNonuniqueness.Section6.MovingPatchCenterGap

noncomputable section

open Set Metric
open scoped BigOperators

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

theorem cascadeCenters_eq_patchCentroid
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (index : Fin count) (patch : Fin 4) :
    trajectory.movingFamily.cascadeCenters time (index, patch) =
      patchCentroid trajectory.movingFamily.patchMotion time index patch := by
  rw [FiniteMovingPatchFamily.patchCentroid_eq]
  exact (trajectory.movingPatch_centroid_eq_center_of_initial_circles initialCircles inside _).symm

theorem cascadeBlockCenter_eq_quadrupoleCenter
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
    cascadeBlockCenter (trajectory.movingFamily.cascadeCenters time) index =
      quadrupoleCenter trajectory.movingFamily.patchMotion time index := by
  unfold cascadeBlockCenter quadrupoleCenter
  congr 1
  exact Finset.sum_congr rfl (fun patch _ => trajectory.cascadeCenters_eq_patchCentroid initialCircles inside index patch)

theorem domain_subset_centroid_ball
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (scales : Scales)
    (radii : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (index : Fin count) (patch : Fin 4) :
    trajectory.movingFamily.patchMotion.domain time index patch ⊆
      closedBall (patchCentroid trajectory.movingFamily.patchMotion time index patch)
        (2 * scales.radius (index.val + 1)) := by
  intro position member
  have bound := (trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).domain_subset_ball_two_radius time member
  rw [mem_ball, dist_eq_norm] at bound
  change ‖position - trajectory.movingFamily.cascadeCenters time (index, patch)‖ <
    2 * configuration.radius (finProdFinEquiv (index, patch)) at bound
  rw [radii, trajectory.cascadeCenters_eq_patchCentroid initialCircles inside] at bound
  exact mem_closedBall.mpr (by simpa only [dist_eq_norm] using bound.le)

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
