import EulerNonuniqueness.Section3.CircleCauchyVariation
import EulerNonuniqueness.Section3.CircleRadialCauchy
import EulerNonuniqueness.Section3.ContourVelocityDerivativeValue

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def diskRelativeHolder (direction : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  holderProduct circleInverseHolder (c1ValueHolder direction)

theorem diskRelativeHolder_value (direction : PeriodicC1HolderHalf) (label : ℝ) :
    (diskRelativeHolder direction).val.1 label = (standardCircle label)⁻¹ * direction.val.1 label := by
  change circleInverseHolder.val.1 label * direction.val.1 label = _
  rw [circleInverseHolder_value]

theorem diskRelativeHolder_conjugate (direction : PeriodicC1HolderHalf) :
    holderConjugate (c1ValueHolder direction) = holderProduct circleInverseHolder (holderConjugate (diskRelativeHolder direction)) := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change star (direction.val.1 label) = circleInverseHolder.val.1 label * star ((diskRelativeHolder direction).val.1 label)
  rw [circleInverseHolder_value, diskRelativeHolder_value]
  have star_inverse : star ((standardCircle label)⁻¹) = standardCircle label := by
    rw [← standardCircle_star_eq_inv, star_star]
  have nonzero : standardCircle label ≠ 0 := norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num)
  rw [star_mul, star_inverse]
  field_simp

theorem disk_contour_linearization_value (direction : PeriodicC1HolderHalf) (target : ℝ) :
    (fderiv ℝ extendedContourVelocity standardCircleBanach direction).val.1 target -
      Complex.I / 2 * direction.val.1 target =
      standardCircle target *
        (-(1 / 2 : ℂ) * (periodicHilbertCLM (holderRealPart (diskRelativeHolder direction))).val.1 target -
          Complex.I / 2 * (holderRealPart (diskRelativeHolder direction)).val.1 target +
          Complex.I / (4 * Real.pi) * ∫ source in (target - Real.pi)..(target + Real.pi),
            (holderRealPart (diskRelativeHolder direction)).val.1 source) := by
  obtain ⟨radius, near, small⟩ := exists_between standardCircleBanach_near
  rw [fderiv_extendedContourVelocity_value standardCircleBanach direction near small target,
    contourVelocityHolderDerivativeCLM_value]
  change Complex.I / 4 * direction.val.1 target - (1 / (4 * Real.pi) : ℂ) *
    star ((contourCauchyDirectionalDerivative standardCircleBanach direction circleInverseHolder).val.1 target +
      (circleCauchyCLM (holderConjugate (c1ValueHolder direction))).val.1 target) - _ = _
  rw [circleCauchy_directionalDerivative_inverse_density, diskRelativeHolder_conjugate,
    circleCauchy_inverse_product (holderConjugate (diskRelativeHolder direction)) target]
  have integral_identity :
      (∫ source in (target - Real.pi)..(target + Real.pi), direction.val.1 source * (standardCircle source)⁻¹) =
      ∫ source in (target - Real.pi)..(target + Real.pi), (diskRelativeHolder direction).val.1 source := by
    apply intervalIntegral.integral_congr
    intro source _
    rw [diskRelativeHolder_value]
    ring
  rw [integral_identity]
  let density := diskRelativeHolder direction
  have inner_identity :
      (standardCircle target)⁻¹ *
          (Complex.I * (∫ source in (target - Real.pi)..(target + Real.pi), density.val.1 source) +
            (circleCauchyCLM density).val.1 target) -
        (Real.pi : ℂ) * Complex.I * direction.val.1 target * ((standardCircle target)⁻¹ * (standardCircle target)⁻¹) +
        ((standardCircle target)⁻¹ * (circleCauchyCLM (holderConjugate density)).val.1 target +
          Complex.I * (standardCircle target)⁻¹ *
            ∫ source in (target - Real.pi)..(target + Real.pi), star (density.val.1 source)) =
      (standardCircle target)⁻¹ *
          (2 * (Real.pi : ℂ) * (periodicHilbertCLM (holderRealPart density)).val.1 target +
            Complex.I * ∫ source in (target - Real.pi)..(target + Real.pi), (holderRealPart density).val.1 source) -
        (Real.pi : ℂ) * Complex.I * direction.val.1 target * ((standardCircle target)⁻¹ * (standardCircle target)⁻¹) := by
    have cauchy := circleCauchy_realPart_sum density target
    have integral := integral_holderRealPart density (target - Real.pi) (target + Real.pi)
    linear_combination (standardCircle target)⁻¹ * cauchy + Complex.I * (standardCircle target)⁻¹ * integral
  change Complex.I / 4 * direction.val.1 target - (1 / (4 * Real.pi) : ℂ) * star
    ((standardCircle target)⁻¹ *
        (Complex.I * (∫ source in (target - Real.pi)..(target + Real.pi), density.val.1 source) +
          (circleCauchyCLM density).val.1 target) -
      (Real.pi : ℂ) * Complex.I * direction.val.1 target * ((standardCircle target)⁻¹ * (standardCircle target)⁻¹) +
      ((standardCircle target)⁻¹ * (circleCauchyCLM (holderConjugate density)).val.1 target +
        Complex.I * (standardCircle target)⁻¹ *
          ∫ source in (target - Real.pi)..(target + Real.pi), star (density.val.1 source))) - _ = _
  rw [inner_identity]
  have hilbert_real := periodicHilbertCLM_real (holderRealPart density) (holderRealPart_real density) target
  have integral_real := integral_holderRealPart_real density (target - Real.pi) (target + Real.pi)
  have circle_star : star (standardCircle target) = (standardCircle target)⁻¹ := standardCircle_star_eq_inv target
  simp only [Complex.star_def] at hilbert_real integral_real circle_star
  simp only [Complex.star_def, map_sub, map_add, map_mul, map_div₀, map_inv₀, map_natCast,
    map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  rw [hilbert_real, integral_real, circle_star]
  rw [holderRealPart_value, diskRelativeHolder_value]
  simp only [Complex.star_def, map_mul, map_inv₀]
  rw [circle_star]
  have nonzero : standardCircle target ≠ 0 := norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num)
  have pi_nonzero : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  dsimp only [density]
  ring_nf
  field_simp [nonzero, pi_nonzero]
  ring_nf
  field_simp [pi_nonzero]
  ring

end

end EulerNonuniqueness.Paper
