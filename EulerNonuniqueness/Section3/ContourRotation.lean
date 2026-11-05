import EulerNonuniqueness.Section3.CrossContourPhaseIdentity
import EulerNonuniqueness.Definitions

namespace EulerNonuniqueness.Paper

noncomputable section

theorem biotSavartKernel_unit_rotation (position rotation : ℂ) (unit_rotation : ‖rotation‖ = 1) :
    biotSavartKernel (rotation * position) = rotation * biotSavartKernel position := by
  unfold biotSavartKernel
  rw [norm_mul, unit_rotation, one_mul]
  ring

theorem pointContourVelocity_unit_rotation (curve tangent : ℝ → ℂ)
    (point rotation center : ℂ) (unit_rotation : ‖rotation‖ = 1) (lower upper : ℝ) :
    pointContourVelocity (fun source => rotation * curve source + center)
        (fun source => rotation * tangent source) (rotation * point + center) lower upper =
      rotation * pointContourVelocity curve tangent point lower upper := by
  unfold pointContourVelocity
  have integrand : (fun source => Real.log
      ‖rotation * curve source + center - (rotation * point + center)‖ • (rotation * tangent source)) =
      (fun source => rotation * (Real.log ‖curve source - point‖ • tangent source)) := by
    funext source
    rw [add_sub_add_right_eq_sub, ← mul_sub, norm_mul, unit_rotation, one_mul]
    simp only [Complex.real_smul]
    ring
  rw [integrand, intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul]
  ring

end

end EulerNonuniqueness.Paper
