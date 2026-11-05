import EulerNonuniqueness.General.RelativeQuadraticTaylor
import EulerNonuniqueness.General.LocalSecondRegularity

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem exists_parameter_lipschitz_quadratic_taylor_ball
    (function : Space → Target) (regular : HasLipschitzSecondDerivativeNear function (0 : Space)) :
    ∃ radius > 0, ∃ constant : NNReal, ∀ initial final increment : Space,
      ‖initial‖ + ‖increment‖ ≤ radius → ‖final‖ + ‖increment‖ ≤ radius →
      ‖(function (initial + increment) - function initial - fderiv ℝ function initial increment) -
        (function (final + increment) - function final - fderiv ℝ function final increment)‖ ≤
        (constant : ℝ) * ‖initial - final‖ * ‖increment‖ ^ 2 := by
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := regular.2.2
  have combined : neighborhood ∩ {point | DifferentiableAt ℝ function point ∧
      DifferentiableAt ℝ (fderiv ℝ function) point} ∈ 𝓝 (0 : Space) := by
    apply inter_mem nearby
    filter_upwards [regular.1.1, regular.2.1] with point first second
    exact ⟨first, second⟩
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  have smaller : closedBall (0 : Space) (radius / 2) ⊆
      neighborhood ∩ {point | DifferentiableAt ℝ function point ∧
        DifferentiableAt ℝ (fderiv ℝ function) point} := by
    intro point member
    apply contained
    have bound := mem_closedBall.mp member
    apply mem_ball.mpr
    linarith
  refine ⟨radius / 2, by positivity, constant, ?_⟩
  intro initial final increment initialInside finalInside
  exact norm_quadratic_taylor_remainder_base_difference function (fderiv ℝ function)
    (fderiv ℝ (fderiv ℝ function)) constant
    (fun point member => (smaller member).2.1.hasFDerivAt)
    (fun point member => (smaller member).2.2.hasFDerivAt)
    (lipschitz.mono fun point member => (smaller member).1)
    initial final increment initialInside finalInside

end

end EulerNonuniqueness.General
