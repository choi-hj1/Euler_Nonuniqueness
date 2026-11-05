import EulerNonuniqueness.Section5.CascadeCoMovingPreparedPair
import EulerNonuniqueness.General.InteriorNormGronwall

noncomputable section

open Set
open scoped BigOperators

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

def blockExtentVector
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) (time : ℝ) : Fin 4 → ℂ :=
  fun patch => trajectory.center (finProdFinEquiv (index, patch)) time -
    (∑ source : Fin 4, trajectory.center (finProdFinEquiv (index, source)) time) / 4

def blockExtentVelocity
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) (time : ℝ) : Fin 4 → ℂ :=
  fun patch => (trajectory.velocity time).2.1 (finProdFinEquiv (index, patch)) -
    (∑ source : Fin 4, (trajectory.velocity time).2.1 (finProdFinEquiv (index, source))) / 4

theorem blockExtentVector_hasDerivAt
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) (time : ℝ) :
    HasDerivAt (trajectory.blockExtentVector index) (trajectory.blockExtentVelocity index time) time := by
  apply (hasDerivAt_pi (𝕜 := ℝ) (E' := fun _ : Fin 4 => ℂ)).mpr
  intro patch
  exact (trajectory.center_hasDerivAt (finProdFinEquiv (index, patch)) time).sub
    ((HasDerivAt.sum (u := Finset.univ) fun source _ =>
      trajectory.center_hasDerivAt (finProdFinEquiv (index, source)) time).div_const 4)

theorem blockExtentVelocity_continuous
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) :
    Continuous (trajectory.blockExtentVelocity index) := by
  apply continuous_pi
  intro patch
  have component (source : Fin 4) :
      Continuous (fun time => (trajectory.velocity time).2.1 (finProdFinEquiv (index, source))) :=
    (continuous_apply (finProdFinEquiv (index, source))).comp
      (continuous_fst.comp (continuous_snd.comp trajectory.velocity_continuous))
  exact (component patch).sub ((continuous_finset_sum Finset.univ fun source _ => component source).div_const 4)

theorem blockExtentVector_gronwall
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (index : Fin count) {horizon rate forcing : ℝ}
    (horizonPositive : 0 < horizon) (rateNonnegative : 0 ≤ rate) (forcingNonnegative : 0 ≤ forcing)
    (bound : ∀ time ∈ Ioo (0 : ℝ) horizon,
      ‖trajectory.blockExtentVelocity index time‖ ≤
        rate * ‖trajectory.blockExtentVector index time‖ + forcing) :
    ∀ time ∈ Icc (0 : ℝ) horizon,
      ‖trajectory.blockExtentVector index time‖ ≤
        (‖trajectory.blockExtentVector index 0‖ + forcing * time) * Real.exp (rate * time) := by
  apply EulerNonuniqueness.General.norm_constant_forcing_gronwall_of_interior_derivative
    horizonPositive rateNonnegative forcingNonnegative
    (continuous_iff_continuousAt.mpr fun time =>
      (trajectory.blockExtentVector_hasDerivAt index time).continuousAt).continuousOn
    (trajectory.blockExtentVelocity_continuous index).continuousOn
    (fun time _ => trajectory.blockExtentVector_hasDerivAt index time) bound

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
