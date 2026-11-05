import EulerNonuniqueness.Section5.CascadeBlockExtentEvolution
import EulerNonuniqueness.Section3.MovingCentroidGaugeConservation

noncomputable section

open Set Filter
open scoped BigOperators

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

theorem blockExtentVector_eq_centroid_offset
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (index : Fin count) (patch : Fin 4) :
    trajectory.blockExtentVector index time patch =
      patchCentroid trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter trajectory.movingFamily.patchMotion time index := by
  have centroid (source : Fin 4) : patchCentroid trajectory.movingFamily.patchMotion time index source =
      trajectory.center (finProdFinEquiv (index, source)) time := by
    rw [FiniteMovingPatchFamily.patchCentroid_eq]
    exact trajectory.movingPatch_centroid_eq_center_of_initial_circles initialCircles inside _
  unfold blockExtentVector quadrupoleCenter
  rw [centroid patch]
  congr 2
  apply Finset.sum_congr rfl
  intro source _
  exact (centroid source).symm

theorem blockExtentVelocity_eq_centroid_offset_deriv
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (index : Fin count) (patch : Fin 4) :
    trajectory.blockExtentVelocity index time patch =
      deriv (fun current => patchCentroid trajectory.movingFamily.patchMotion current index patch -
        quadrupoleCenter trajectory.movingFamily.patchMotion current index) time := by
  have derivative := ((hasDerivAt_pi (𝕜 := ℝ) (E' := fun _ : Fin 4 => ℂ)).mp
    (trajectory.blockExtentVector_hasDerivAt index time)) patch
  have equality : (fun current => patchCentroid trajectory.movingFamily.patchMotion current index patch -
      quadrupoleCenter trajectory.movingFamily.patchMotion current index) =ᶠ[nhds time]
      (fun current => trajectory.blockExtentVector index current patch) := by
    filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
    exact (trajectory.blockExtentVector_eq_centroid_offset initialCircles member index patch).symm
  exact (derivative.congr_of_eventuallyEq equality).deriv.symm

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
