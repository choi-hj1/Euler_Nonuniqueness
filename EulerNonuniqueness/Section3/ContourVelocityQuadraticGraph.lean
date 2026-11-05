import EulerNonuniqueness.Section3.ContourVelocityAmbientCubicTaylor
import EulerNonuniqueness.Section3.ClosedSubmoduleQuadratic

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem contourVelocityAmbientQuadratic_mem (data direction : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourVelocityAmbientQuadratic data direction ∈ periodicC1HolderGraph := by
  obtain ⟨radius, near, radius_small⟩ := exists_between small
  let linear := contourVelocityAmbientDerivativeCLM data near radius_small direction
  let quadratic := contourVelocityAmbientQuadratic data direction
  let function : ℝ → periodicC1HolderGraph := fun parameter =>
    extendedContourVelocity (data + parameter • direction)
  have linear_mem : linear ∈ periodicC1HolderGraph :=
    contourVelocityAmbientDerivative_mem data direction near radius_small
  have radius_lt_one : radius < 1 := radius_small.trans_le (min_le_left _ _)
  let incrementRadius := min ((radius - ‖data - standardCircleBanach‖) / 4)
    (min ((1 - radius) / 2) 1)
  have increment_positive : 0 < incrementRadius := by
    dsimp only [incrementRadius]
    exact lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have parameter_positive : 0 < incrementRadius / (‖direction‖ + 1) :=
    div_pos increment_positive (by positivity)
  have remainder_bigO : (fun parameter : ℝ => (function parameter : C1HolderGraphAmbient) -
      (function 0 : C1HolderGraphAmbient) - parameter • linear - parameter ^ 2 • quadratic)
      =O[𝓝 0] (fun parameter : ℝ => ‖parameter‖ ^ 3) := by
    apply Asymptotics.IsBigO.of_bound
      (contourVelocityAmbientCubicBound data ‖data - standardCircleBanach‖ radius * ‖direction‖ ^ 3)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) parameter_positive] with parameter member
    have parameter_small : ‖parameter‖ < incrementRadius / (‖direction‖ + 1) := by
      simpa only [mem_ball, dist_zero_right] using member
    have product_small := (lt_div_iff₀ (by positivity : (0 : ℝ) < ‖direction‖ + 1)).mp parameter_small
    have increment_small : ‖parameter • direction‖ ≤ incrementRadius := by
      rw [norm_smul parameter direction]
      nlinarith [norm_nonneg parameter]
    have first_small : ‖parameter • direction‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4 :=
      increment_small.trans (min_le_left _ _)
    have inverse_small : ‖parameter • direction‖ ≤ (1 - radius) / 2 :=
      increment_small.trans ((min_le_right _ _).trans (min_le_left _ _))
    have increment_bound : ‖parameter • direction‖ ≤ 1 :=
      increment_small.trans ((min_le_right _ _).trans (min_le_right _ _))
    have actual := contourVelocityAmbient_cubic_taylor_bound data (parameter • direction)
      (norm_nonneg _) near radius_small le_rfl first_small inverse_small increment_bound
    rw [(contourVelocityAmbientDerivativeCLM data near radius_small).map_smul parameter direction,
      contourVelocityAmbientQuadratic_real_smul data direction small parameter,
      norm_smul parameter direction] at actual
    have bound_identity :
        contourVelocityAmbientCubicBound data ‖data - standardCircleBanach‖ radius *
            (‖parameter‖ * ‖direction‖) ^ 3 =
          (contourVelocityAmbientCubicBound data ‖data - standardCircleBanach‖ radius * ‖direction‖ ^ 3) *
            ‖‖parameter‖ ^ 3‖ := by
      simp only [Real.norm_eq_abs, abs_pow, abs_abs]
      ring
    simpa only [function, linear, quadratic, zero_smul, add_zero, bound_identity] using actual
  have little_norm := remainder_bigO.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_norm_pow (E' := ℝ) (by decide : 2 < (3 : ℕ)))
  have little : (fun parameter : ℝ => (function parameter : C1HolderGraphAmbient) -
      (function 0 : C1HolderGraphAmbient) - parameter • linear - parameter ^ 2 • quadratic)
      =o[𝓝 0] (fun parameter : ℝ => parameter ^ 2) := by
    apply Asymptotics.isLittleO_norm_right.mp
    simpa only [norm_pow] using little_norm
  exact closedSubmodule_quadratic_coefficient_mem periodicC1HolderGraph periodicC1HolderGraph_isClosed
    function linear quadratic linear_mem (little.mono nhdsWithin_le_nhds)

end

end EulerNonuniqueness.Paper
