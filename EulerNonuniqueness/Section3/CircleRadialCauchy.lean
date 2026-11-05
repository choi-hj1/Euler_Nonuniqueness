import EulerNonuniqueness.Section3.CircleCauchyHilbertIdentity

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

def holderRealPart (density : PeriodicHolderHalf) : PeriodicHolderHalf :=
  (1 / 2 : ℝ) • (density + holderConjugate density)

theorem holderRealPart_value (density : PeriodicHolderHalf) (label : ℝ) :
    (holderRealPart density).val.1 label = (1 / 2 : ℂ) * (density.val.1 label + star (density.val.1 label)) := by
  change ((1 / 2 : ℝ) : ℂ) * _ = _
  push_cast
  rfl

theorem holderRealPart_real (density : PeriodicHolderHalf) (label : ℝ) :
    star ((holderRealPart density).val.1 label) = (holderRealPart density).val.1 label := by
  rw [holderRealPart_value]
  simp only [Complex.star_def, map_mul, map_add, map_div₀, map_one, map_ofNat, Complex.conj_conj]
  ring

theorem integral_holderRealPart (density : PeriodicHolderHalf) (lower upper : ℝ) :
    (∫ source in lower..upper, density.val.1 source) +
      (∫ source in lower..upper, star (density.val.1 source)) =
      2 * ∫ source in lower..upper, (holderRealPart density).val.1 source := by
  simp_rw [holderRealPart_value]
  have conjugate_integrable : IntervalIntegrable (fun source => star (density.val.1 source))
      volume lower upper := (continuous_star.comp density.val.1.continuous).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (density.val.1.continuous.intervalIntegrable _ _)
    conjugate_integrable]
  ring

theorem circleCauchy_realPart_sum (density : PeriodicHolderHalf) (target : ℝ) :
    (circleCauchyCLM density).val.1 target + (circleCauchyCLM (holderConjugate density)).val.1 target =
      2 * (Real.pi : ℂ) * (periodicHilbertCLM (holderRealPart density)).val.1 target -
        Complex.I * ∫ source in (target - Real.pi)..(target + Real.pi), (holderRealPart density).val.1 source := by
  have radial := congrArg (fun data : PeriodicHolderHalf => data.val.1 target)
    (circleCauchyCLM.map_smul (1 / 2 : ℝ) (density + holderConjugate density))
  rw [map_add] at radial
  change (circleCauchyCLM (holderRealPart density)).val.1 target =
    (1 / 2 : ℝ) • ((circleCauchyCLM density).val.1 target +
      (circleCauchyCLM (holderConjugate density)).val.1 target) at radial
  rw [circleCauchyCLM_eq_hilbert_integral, Complex.real_smul] at radial
  push_cast at radial
  linear_combination -2 * radial

theorem integral_holderRealPart_real (density : PeriodicHolderHalf) (lower upper : ℝ) :
    star (∫ source in lower..upper, (holderRealPart density).val.1 source) =
      ∫ source in lower..upper, (holderRealPart density).val.1 source := by
  have identity : (∫ source in lower..upper, star ((holderRealPart density).val.1 source)) =
      star (∫ source in lower..upper, (holderRealPart density).val.1 source) :=
    Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
      ((holderRealPart density).val.1.continuous.intervalIntegrable _ _)
  simp_rw [holderRealPart_real] at identity
  exact identity.symm

end

end EulerNonuniqueness.Paper
