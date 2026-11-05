import EulerNonuniqueness.Section3.CircleCauchyCommutator

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem circleCauchy_variation_kernel {target source valueTarget valueSource tangentSource : ℂ}
    (target_ne : target ≠ 0) (source_ne : source ≠ 0) (separated : target - source ≠ 0) :
    (source⁻¹ - target⁻¹) * (tangentSource / (target - source) -
      Complex.I * source * (valueTarget - valueSource) / (target - source) ^ 2) =
      target⁻¹ * (tangentSource * source⁻¹ +
        (source⁻¹ * valueSource - target⁻¹ * valueTarget) * (Complex.I * source) / (target - source)) -
      Complex.I * valueTarget * (target⁻¹ * target⁻¹) := by
  generalize difference_eq : target - source = difference at separated ⊢
  ring_nf
  field_simp [target_ne, source_ne, separated]
  rw [← difference_eq]
  ring

theorem integral_circle_inverse_tangent (direction : PeriodicC1HolderHalf) (target : ℝ) :
    (∫ source in (target - Real.pi)..(target + Real.pi),
      direction.val.2.val.1 source * (standardCircle source)⁻¹) =
      Complex.I * ∫ source in (target - Real.pi)..(target + Real.pi),
        direction.val.1 source * (standardCircle source)⁻¹ := by
  have derivative (source : ℝ) : HasDerivAt
      (fun parameter => direction.val.1 parameter * star (standardCircle parameter))
      (direction.val.2.val.1 source * star (standardCircle source) -
        Complex.I * (direction.val.1 source * star (standardCircle source))) source := by
    have actual := (PeriodicC1HolderHalf.hasDerivAt direction source).mul (standardCircle_derivative source).star
    convert actual using 1
    simp only [standardCircleTangent, Complex.star_def, map_mul, Complex.conj_I]
    ring
  have first : IntervalIntegrable (fun source => direction.val.2.val.1 source * star (standardCircle source))
      volume (target - Real.pi) (target + Real.pi) :=
    (direction.val.2.val.1.continuous.mul standardCircleBanach.val.1.continuous.star).intervalIntegrable _ _
  have second : IntervalIntegrable (fun source => direction.val.1 source * star (standardCircle source))
      volume (target - Real.pi) (target + Real.pi) :=
    (direction.val.1.continuous.mul standardCircleBanach.val.1.continuous.star).intervalIntegrable _ _
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun source _ => derivative source)
    (first.sub (second.const_mul Complex.I))
  have direction_closed : direction.val.1 (target + Real.pi) = direction.val.1 (target - Real.pi) := by
    have periodic := PeriodicC1HolderHalf.periodic direction (target - Real.pi)
    convert periodic using 1 <;> congr 1 <;> ring
  have circle_closed : standardCircle (target + Real.pi) = standardCircle (target - Real.pi) := by
    have periodic := standardCircle_periodic (target - Real.pi)
    convert periodic using 1 <;> congr 1 <;> ring
  rw [intervalIntegral.integral_sub first (second.const_mul Complex.I), intervalIntegral.integral_const_mul,
    direction_closed, circle_closed, sub_self, sub_eq_zero] at integral
  simpa only [standardCircle_star_eq_inv] using integral

theorem circleCauchy_directionalDerivative_inverse_density (direction : PeriodicC1HolderHalf) (target : ℝ) :
    (contourCauchyDirectionalDerivative standardCircleBanach direction circleInverseHolder).val.1 target =
      (standardCircle target)⁻¹ *
        (Complex.I * (∫ source in (target - Real.pi)..(target + Real.pi),
          direction.val.1 source * (standardCircle source)⁻¹) +
          (circleCauchyCLM (holderProduct circleInverseHolder (c1ValueHolder direction))).val.1 target) -
        (Real.pi : ℂ) * Complex.I * direction.val.1 target * ((standardCircle target)⁻¹ * (standardCircle target)⁻¹) := by
  let density := holderProduct circleInverseHolder (c1ValueHolder direction)
  have density_value (source : ℝ) : density.val.1 source = (standardCircle source)⁻¹ * direction.val.1 source := by
    change circleInverseHolder.val.1 source * direction.val.1 source = _
    rw [circleInverseHolder_value]
  have first : IntervalIntegrable
      (fun source => direction.val.2.val.1 source * (standardCircle source)⁻¹)
      volume (target - Real.pi) (target + Real.pi) := by
    simp_rw [← standardCircle_star_eq_inv]
    exact (direction.val.2.val.1.continuous.mul standardCircleBanach.val.1.continuous.star).intervalIntegrable _ _
  have second := contourCauchyDensityRemainder_intervalIntegrable standardCircleBanach density
    (standardCircleBanach_near.trans_le (min_le_right _ _)) target
  change IntervalIntegrable (contourCauchyDensityRemainder standardCircle standardCircleTangent density.val.1 target)
    volume (target - Real.pi) (target + Real.pi) at second
  have integral_identity :
      (∫ source in (target - Real.pi)..(target + Real.pi),
        (circleInverseHolder.val.1 source - circleInverseHolder.val.1 target) *
          contourCauchyKernelVariation standardCircleBanach direction target source) =
      ∫ source in (target - Real.pi)..(target + Real.pi),
        (standardCircle target)⁻¹ * (direction.val.2.val.1 source * (standardCircle source)⁻¹ +
          contourCauchyDensityRemainder standardCircle standardCircleTangent density.val.1 target source) -
        Complex.I * direction.val.1 target * ((standardCircle target)⁻¹ * (standardCircle target)⁻¹) := by
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
    simp only [circleInverseHolder_value]
    unfold contourCauchyKernelVariation contourCauchyDensityRemainder
    rw [density_value source, density_value target]
    change ((standardCircle source)⁻¹ - (standardCircle target)⁻¹) *
      (direction.val.2.val.1 source / (standardCircle target - standardCircle source) -
        (Complex.I * standardCircle source) * (direction.val.1 target - direction.val.1 source) /
          (standardCircle target - standardCircle source) ^ 2) =
      (standardCircle target)⁻¹ * (direction.val.2.val.1 source * (standardCircle source)⁻¹ +
        ((standardCircle source)⁻¹ * direction.val.1 source - (standardCircle target)⁻¹ * direction.val.1 target) *
          (Complex.I * standardCircle source) / (standardCircle target - standardCircle source)) - _
    exact circleCauchy_variation_kernel
      (norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num))
      (norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num)) separated
  rw [contourCauchyDirectionalDerivative_value standardCircleBanach direction circleInverseHolder standardCircleBanach_near,
    integral_identity, intervalIntegral.integral_sub ((first.add second).const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add first second,
    integral_circle_inverse_tangent, intervalIntegral.integral_const]
  change _ = (standardCircle target)⁻¹ * (_ +
    contourCauchyTransform standardCircle standardCircleTangent density.val.1 target) - _
  unfold contourCauchyTransform
  rw [density_value target]
  rw [Complex.real_smul]
  push_cast
  ring

end

end EulerNonuniqueness.Paper
