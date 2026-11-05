import Mathlib.Analysis.ODE.Gronwall

noncomputable section

open Set
open scoped NNReal Topology

namespace EulerNonuniqueness

theorem dist_flow_linearization_le {Space : Type*}
    [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    {field flow : ℝ → Space → Space} {jacobian coefficient : ℝ → Space →L[ℝ] Space}
    {horizon : ℝ} {bound : ℝ≥0} (lipschitz : ∀ time, LipschitzWith bound (field time))
    (initial : ∀ position, flow 0 position = position)
    (continuous : ∀ position, ContinuousOn (fun time => flow time position) (Icc 0 horizon))
    (equation : ∀ position time, time ∈ Ico 0 horizon →
      HasDerivWithinAt (fun next => flow next position) (field time (flow time position)) (Ici time) time)
    (jacobianInitial : jacobian 0 = ContinuousLinearMap.id ℝ Space)
    (jacobianContinuous : ContinuousOn jacobian (Icc 0 horizon))
    (jacobianEquation : ∀ direction time, time ∈ Ico 0 horizon →
      HasDerivWithinAt (fun next => jacobian next direction)
        (coefficient time (jacobian time direction)) (Ici time) time)
    (position increment : Space) {error : ℝ}
    (remainder : ∀ time ∈ Ico 0 horizon,
      dist (field time (flow time position) + coefficient time (jacobian time increment))
        (field time (flow time position + jacobian time increment)) ≤ error * ‖increment‖)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    dist (flow time (position + increment)) (flow time position + jacobian time increment) ≤
      gronwallBound 0 bound (error * ‖increment‖) time := by
  have estimate := dist_le_of_approx_trajectories_ODE lipschitz
    (continuous (position + increment)) (equation (position + increment))
    (fun _ _ => by simp only [dist_self]; exact le_rfl)
    ((continuous position).add (jacobianContinuous.clm_apply continuousOn_const))
    (fun next nextInside => (equation position next nextInside).add
      (jacobianEquation increment next nextInside)) remainder
    (δ := 0) (by simp [initial, jacobianInitial]) time inside
  simpa only [zero_add, sub_zero] using estimate

end EulerNonuniqueness
