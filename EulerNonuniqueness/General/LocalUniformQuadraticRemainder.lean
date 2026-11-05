import EulerNonuniqueness.General.LipschitzDerivativeQuadraticRemainder
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

namespace EulerNonuniqueness.General

noncomputable section

open Filter Metric
open scoped Topology

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem HasLipschitzDerivativeNear.exists_uniform_quadratic_remainder
    (function : Space → Target) (regular : HasLipschitzDerivativeNear function (0 : Space)) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ base increment : Space,
      ‖base‖ + ‖increment‖ ≤ radius →
      ‖function (base + increment) - function base - fderiv ℝ function base increment‖ ≤ constant * ‖increment‖ ^ 2 := by
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := regular.2
  have combined : neighborhood ∩ {value | DifferentiableAt ℝ function value} ∈ 𝓝 (0 : Space) :=
    inter_mem nearby regular.1
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  have smaller : closedBall (0 : Space) (radius / 2) ⊆ neighborhood ∩ {value | DifferentiableAt ℝ function value} := by
    intro value member
    apply contained
    have bound := Metric.mem_closedBall.mp member
    apply Metric.mem_ball.mpr
    linarith
  refine ⟨radius / 2, by positivity, (constant : ℝ), constant.coe_nonneg, ?_⟩
  intro base increment inside
  exact norm_quadratic_remainder_of_lipschitz_derivative function (fderiv ℝ function) constant
    (fun value member => (smaller member).2.hasFDerivAt) (lipschitz.mono fun _ member => (smaller member).1)
    base increment inside

end

end EulerNonuniqueness.General
