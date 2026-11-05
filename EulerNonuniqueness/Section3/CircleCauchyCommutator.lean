import EulerNonuniqueness.Section3.ContourVelocityFrechet
import EulerNonuniqueness.Section3.PeriodicHilbertModes

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem standardCircle_star_eq_inv (label : ℝ) : star (standardCircle label) = (standardCircle label)⁻¹ := by
  have nonzero : standardCircle label ≠ 0 := norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num)
  apply mul_left_cancel₀ nonzero
  rw [mul_inv_cancel₀ nonzero]
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, standardCircle_norm]
  norm_num

def circleInverseHolder : PeriodicHolderHalf := holderConjugate (c1ValueHolder standardCircleBanach)

theorem circleInverseHolder_value (label : ℝ) : circleInverseHolder.val.1 label = (standardCircle label)⁻¹ :=
  standardCircle_star_eq_inv label

theorem circleCauchy_inverse_product_kernel {target source densityTarget densitySource : ℂ}
    (target_ne : target ≠ 0) (source_ne : source ≠ 0) (separated : target - source ≠ 0) :
    ((source⁻¹ * densitySource) - target⁻¹ * densityTarget) * (Complex.I * source) / (target - source) =
      target⁻¹ * ((densitySource - densityTarget) * (Complex.I * source) / (target - source)) +
        Complex.I * target⁻¹ * densitySource := by
  field_simp
  ring

theorem circleCauchy_inverse_product (density : PeriodicHolderHalf) (target : ℝ) :
    (circleCauchyCLM (holderProduct circleInverseHolder density)).val.1 target =
      (standardCircle target)⁻¹ * (circleCauchyCLM density).val.1 target +
        Complex.I * (standardCircle target)⁻¹ * ∫ source in (target - Real.pi)..(target + Real.pi), density.val.1 source := by
  have second := contourCauchyDensityRemainder_intervalIntegrable standardCircleBanach density
    (standardCircleBanach_near.trans_le (min_le_right _ _)) target
  change IntervalIntegrable (contourCauchyDensityRemainder standardCircle standardCircleTangent density.val.1 target)
    volume (target - Real.pi) (target + Real.pi) at second
  have density_integrable := density.val.1.continuous.intervalIntegrable (μ := volume)
    (target - Real.pi) (target + Real.pi)
  have integral_identity :
      (∫ source in (target - Real.pi)..(target + Real.pi),
        contourCauchyDensityRemainder standardCircle standardCircleTangent
          (holderProduct circleInverseHolder density).val.1 target source) =
      (standardCircle target)⁻¹ *
        (∫ source in (target - Real.pi)..(target + Real.pi),
          contourCauchyDensityRemainder standardCircle standardCircleTangent density.val.1 target source) +
        Complex.I * (standardCircle target)⁻¹ *
          ∫ source in (target - Real.pi)..(target + Real.pi), density.val.1 source := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (second.const_mul ((standardCircle target)⁻¹))
        (density_integrable.const_mul (Complex.I * (standardCircle target)⁻¹))]
    apply intervalIntegral.integral_congr_ae
    have almost_distinct : ∀ᵐ source : ℝ ∂volume, source ≠ target := by simp [ae_iff]
    filter_upwards [almost_distinct] with source distinct
    intro member
    rw [uIoc_of_le (by linarith [Real.pi_pos])] at member
    have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [member.1, member.2, Real.pi_pos]
    have chord := standardCircle_chord_bound_extended nearby
    rw [norm_sub_rev (standardCircle source) (standardCircle target)] at chord
    have separated : standardCircle target - standardCircle source ≠ 0 :=
      norm_ne_zero_iff.mp (ne_of_gt ((mul_pos (by positivity : 0 < 2 / (3 * Real.pi))
        (abs_pos.mpr (sub_ne_zero.mpr distinct))).trans_le chord))
    unfold contourCauchyDensityRemainder
    simp only [holderProduct_value, circleInverseHolder_value]
    exact circleCauchy_inverse_product_kernel
      (norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num))
      (norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num)) separated
  change contourCauchyTransform standardCircle standardCircleTangent
      (holderProduct circleInverseHolder density).val.1 target =
    (standardCircle target)⁻¹ * contourCauchyTransform standardCircle standardCircleTangent density.val.1 target + _
  unfold contourCauchyTransform
  rw [integral_identity, holderProduct_value, circleInverseHolder_value]
  ring

end

end EulerNonuniqueness.Paper
