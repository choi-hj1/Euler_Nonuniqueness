import EulerNonuniqueness.Section3.MovingCentroidGaugeJointFamily
import EulerNonuniqueness.Section3.MovingCentroidGaugeConservation
import EulerNonuniqueness.Section3.FiniteMovingPatchMotion

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance jointCentroidsHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance jointCentroidsC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

variable {Parameter : Type*} [TopologicalSpace Parameter]
  {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : Parameter → MovingContourState (count * 4)}

theorem joint_patchCentroid_continuousOn_interior
    (trajectories : (parameter : Parameter) →
      MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon (initial parameter))
    (jointContinuous : Continuous (fun point : Parameter × ℝ => (trajectories point.1).curve point.2))
    (initialCircles : ∀ parameter index, (initial parameter).2.2 index = standardCircleBanach)
    (index : Fin count) (patch : Fin 4) :
    ContinuousOn (fun point : Parameter × ℝ =>
      patchCentroid (trajectories point.1).movingFamily.patchMotion point.2 index patch)
      {point | point.2 ∈ Ioo (-backwardHorizon) forwardHorizon} := by
  have centerContinuous := joint_center_continuousOn_interior trajectories jointContinuous (finProdFinEquiv (index, patch))
  apply centerContinuous.congr
  intro point inside
  change patchCentroid (trajectories point.1).movingFamily.patchMotion point.2 index patch =
    (trajectories point.1).center (finProdFinEquiv (index, patch)) point.2
  rw [FiniteMovingPatchFamily.patchCentroid_eq]
  exact (trajectories point.1).movingPatch_centroid_eq_center_of_initial_circles
    (initialCircles point.1) inside (finProdFinEquiv (index, patch))

theorem joint_quadrupoleCenter_continuousOn_interior
    (trajectories : (parameter : Parameter) →
      MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon (initial parameter))
    (jointContinuous : Continuous (fun point : Parameter × ℝ => (trajectories point.1).curve point.2))
    (initialCircles : ∀ parameter index, (initial parameter).2.2 index = standardCircleBanach)
    (index : Fin count) :
    ContinuousOn (fun point : Parameter × ℝ =>
      quadrupoleCenter (trajectories point.1).movingFamily.patchMotion point.2 index)
      {point | point.2 ∈ Ioo (-backwardHorizon) forwardHorizon} := by
  have summed : ContinuousOn (fun point : Parameter × ℝ =>
      ∑ patch : Fin 4, patchCentroid (trajectories point.1).movingFamily.patchMotion point.2 index patch)
      {point | point.2 ∈ Ioo (-backwardHorizon) forwardHorizon} := by
    apply continuousOn_finset_sum
    intro patch _member
    exact joint_patchCentroid_continuousOn_interior trajectories jointContinuous initialCircles index patch
  exact summed.div_const 4

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
