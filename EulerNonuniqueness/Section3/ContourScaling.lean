import EulerNonuniqueness.Section3.CrossContourPhaseIdentity

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem pointContourVelocity_scaling (curve tangent : ℝ → ℂ) (point center : ℂ)
    {radius lower upper : ℝ} (radius_pos : 0 < radius)
    (tangent_integrable : IntervalIntegrable tangent volume lower upper)
    (log_integrable : IntervalIntegrable (fun source => Real.log ‖curve source - point‖ • tangent source)
      volume lower upper)
    (separated : ∀ᵐ source ∂volume, source ∈ uIoc lower upper → curve source - point ≠ 0)
    (tangent_zero : (∫ source in lower..upper, tangent source) = 0) :
    pointContourVelocity (fun source => center + radius • curve source)
      (fun source => radius • tangent source) (center + radius • point) lower upper =
      radius • pointContourVelocity curve tangent point lower upper := by
  have integrands :
      (∫ source in lower..upper,
        Real.log ‖(center + radius • curve source) - (center + radius • point)‖ • (radius • tangent source)) =
      ∫ source in lower..upper,
        radius • (Real.log radius • tangent source + Real.log ‖curve source - point‖ • tangent source) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [separated] with source source_sep source_mem
    have difference : (center + radius • curve source) - (center + radius • point) =
        radius • (curve source - point) := by rw [smul_sub]; abel
    rw [difference, norm_smul, Real.norm_eq_abs, abs_of_pos radius_pos,
      Real.log_mul radius_pos.ne' (norm_ne_zero_iff.mpr (source_sep source_mem))]
    simp only [add_smul, smul_add, smul_smul]
    rw [← add_smul]
    congr 1
    ring
  have integral_identity :
      (∫ source in lower..upper,
        Real.log ‖(center + radius • curve source) - (center + radius • point)‖ • (radius • tangent source)) =
      radius • ∫ source in lower..upper, Real.log ‖curve source - point‖ • tangent source := by
    have constant_log_integrable : IntervalIntegrable (fun source => Real.log radius • tangent source)
        volume lower upper := tangent_integrable.smul (Real.log radius)
    rw [integrands, intervalIntegral.integral_smul,
      intervalIntegral.integral_add constant_log_integrable log_integrable,
      intervalIntegral.integral_smul, tangent_zero, smul_zero, zero_add]
  rw [pointContourVelocity, pointContourVelocity, integral_identity, smul_smul, smul_smul]
  congr 1
  ring

end

end EulerNonuniqueness.Paper
