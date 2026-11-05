import EulerNonuniqueness.Section5.CascadeMaterialCenterGeometry

noncomputable section

open Set Filter

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

theorem center_velocity_eq_patchCentroid_deriv {count : ℕ}
    {configuration : FiniteContourConfiguration (count * 4)}
    {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (index : Fin count) (patch : Fin 4) :
    (trajectory.velocity time).2.1 (finProdFinEquiv (index, patch)) =
      deriv (fun current => patchCentroid trajectory.movingFamily.patchMotion current index patch) time := by
  have equality : (fun current => patchCentroid trajectory.movingFamily.patchMotion current index patch) =ᶠ[nhds time]
      trajectory.center (finProdFinEquiv (index, patch)) := by
    filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
    exact (trajectory.cascadeCenters_eq_patchCentroid initialCircles member index patch).symm
  exact ((trajectory.center_hasDerivAt (finProdFinEquiv (index, patch)) time).congr_of_eventuallyEq equality).deriv.symm

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
