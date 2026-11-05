import EulerNonuniqueness.Section6.DiskPolarIntegration
import EulerNonuniqueness.Section6.PatchCentroidGeometry

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem integral_zero_ball_norm_sq {radius : ℝ} (radiusPositive : 0 < radius) :
    (∫ position in Metric.ball (0 : ℂ) radius, ‖position‖ ^ 2) = Real.pi * radius ^ 4 / 2 := by
  rw [integral_ball_polar radiusPositive (fun position : ℂ => ‖position‖ ^ 2)
    (continuous_norm.pow 2).continuousOn]
  have angularIntegral (radial : ℝ) :
      (∫ angle in Ioo (-Real.pi) Real.pi,
        radial • ‖(radial : ℂ) * Paper.standardCircle angle‖ ^ 2) =
        2 * Real.pi * radial ^ 3 := by
    simp only [norm_mul, Paper.standardCircle_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, smul_eq_mul]
    rw [integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.toReal_ofReal (show 0 ≤ Real.pi - -Real.pi by linarith [Real.pi_pos]), smul_eq_mul]
    ring
  simp_rw [angularIntegral]
  rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le radiusPositive.le]
  norm_num [integral_pow]
  ring

theorem integral_ball_centered_norm_sq (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius) :
    (∫ position in Metric.ball center radius, ‖position - center‖ ^ 2) = Real.pi * radius ^ 4 / 2 := by
  have substitution := (measurePreserving_add_left (volume : Measure ℂ) center).setIntegral_preimage_emb
    (Homeomorph.addLeft center).toMeasurableEquiv.measurableEmbedding
    (fun position : ℂ => ‖position - center‖ ^ 2) (Metric.ball center radius)
  have preimage : (fun position : ℂ => center + position) ⁻¹' Metric.ball center radius =
      Metric.ball (0 : ℂ) radius := by
    ext position
    simp [Metric.mem_ball, dist_eq_norm]
  rw [preimage] at substitution
  simp only [add_sub_cancel_left] at substitution
  exact substitution.symm.trans (integral_zero_ball_norm_sq radiusPositive)

end EulerNonuniqueness.Section6
