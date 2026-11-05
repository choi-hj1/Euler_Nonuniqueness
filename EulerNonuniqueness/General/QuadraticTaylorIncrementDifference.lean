import EulerNonuniqueness.General.LipschitzDerivativeQuadraticRemainder
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

open Set Metric
open Filter
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem norm_quadratic_taylor_remainder_increment_difference
    (function : Space → Target) (first : Space → Space →L[ℝ] Target)
    {radius : ℝ} (constant : NNReal)
    (actualFirst : ∀ value ∈ closedBall (0 : Space) radius, HasFDerivAt function (first value) value)
    (lipschitz : LipschitzOnWith constant first (closedBall (0 : Space) radius))
    (base initial final : Space)
    (inside : ‖base‖ + (‖initial‖ + ‖final‖) ≤ radius) :
    ‖(function (base + initial) - function base - first base initial) -
      (function (base + final) - function base - first base final)‖ ≤
      (constant : ℝ) * (‖initial‖ + ‖final‖) * ‖initial - final‖ := by
  let remainder := fun point => function (base + point) - function base - first base point
  have contained (point : Space) (member : point ∈ closedBall (0 : Space) (‖initial‖ + ‖final‖)) :
      base + point ∈ closedBall (0 : Space) radius := by
    apply mem_closedBall_zero_iff.mpr
    exact (norm_add_le _ _).trans
      ((add_le_add_left (mem_closedBall_zero_iff.mp member) ‖base‖).trans inside)
  have baseInside : base ∈ closedBall (0 : Space) radius := by
    apply mem_closedBall_zero_iff.mpr
    linarith [norm_nonneg initial, norm_nonneg final]
  have actual (point : Space) (member : point ∈ closedBall (0 : Space) (‖initial‖ + ‖final‖)) :
      HasFDerivAt remainder (first (base + point) - first base) point := by
    have translation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add base
    simpa only [remainder, Function.comp_def, ContinuousLinearMap.comp_id] using
      (((actualFirst _ (contained point member)).comp point translation).sub_const (function base)).sub
        ((first base).hasFDerivAt (x := point))
  have derivativeBound (point : Space) (member : point ∈ closedBall (0 : Space) (‖initial‖ + ‖final‖)) :
      ‖first (base + point) - first base‖ ≤ (constant : ℝ) * (‖initial‖ + ‖final‖) := by
    have estimate := LipschitzOnWith.norm_sub_le (f := first) lipschitz (contained point member) baseInside
    rw [add_sub_cancel_left] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp member) constant.coe_nonneg)
  have initialInside : initial ∈ closedBall (0 : Space) (‖initial‖ + ‖final‖) :=
    mem_closedBall_zero_iff.mpr (le_add_of_nonneg_right (norm_nonneg final))
  have finalInside : final ∈ closedBall (0 : Space) (‖initial‖ + ‖final‖) :=
    mem_closedBall_zero_iff.mpr (le_add_of_nonneg_left (norm_nonneg initial))
  have estimate := (convex_closedBall (0 : Space) (‖initial‖ + ‖final‖)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun point member => (actual point member).hasFDerivWithinAt) derivativeBound initialInside finalInside
  rw [norm_sub_rev (remainder final) (remainder initial), norm_sub_rev final initial] at estimate
  exact estimate

theorem exists_increment_linear_quadratic_taylor_ball
    (function : Space → Target) (regular : HasLipschitzDerivativeNear function (0 : Space)) :
    ∃ radius > 0, ∃ constant : NNReal, ∀ base initial final : Space,
      ‖base‖ + (‖initial‖ + ‖final‖) ≤ radius →
      ‖(function (base + initial) - function base - fderiv ℝ function base initial) -
        (function (base + final) - function base - fderiv ℝ function base final)‖ ≤
        (constant : ℝ) * (‖initial‖ + ‖final‖) * ‖initial - final‖ := by
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := regular.2
  have combined : neighborhood ∩ {point | DifferentiableAt ℝ function point} ∈ 𝓝 (0 : Space) :=
    inter_mem nearby regular.1
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  have smaller : closedBall (0 : Space) (radius / 2) ⊆
      neighborhood ∩ {point | DifferentiableAt ℝ function point} := by
    intro point member
    apply contained
    have bound := mem_closedBall.mp member
    apply mem_ball.mpr
    linarith
  refine ⟨radius / 2, by positivity, constant, ?_⟩
  intro base initial final inside
  exact norm_quadratic_taylor_remainder_increment_difference function (fderiv ℝ function) constant
    (fun point member => (smaller member).2.hasFDerivAt)
    (lipschitz.mono fun point member => (smaller member).1) base initial final inside

end

end EulerNonuniqueness.General
