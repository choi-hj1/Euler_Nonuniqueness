import EulerNonuniqueness.Section3.CircleCauchyCommutator

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem circleCauchyCLM_conjugate (density : PeriodicHolderHalf) (target : ℝ) :
    (circleCauchyCLM (holderConjugate density)).val.1 target =
      star ((circleCauchyCLM density).val.1 target) -
        Complex.I * ∫ source in (target - Real.pi)..(target + Real.pi), star (density.val.1 source) := by
  have actual := circleCauchyCLM_conjugate_zero (holderLabelShift target density)
  rw [holderConjugate_shift, circleCauchyCLM_shift, circleCauchyCLM_shift] at actual
  simp only [holderLabelShift_value, zero_add] at actual
  rw [intervalIntegral.integral_comp_add_right (fun source : ℝ => star (density.val.1 source)) target] at actual
  have left : -Real.pi + target = target - Real.pi := by ring
  have right : Real.pi + target = target + Real.pi := by ring
  simpa only [left, right] using actual

theorem circleCauchyCLM_eq_hilbert_integral (density : PeriodicHolderHalf) (target : ℝ) :
    (circleCauchyCLM density).val.1 target =
      (Real.pi : ℂ) * (periodicHilbertCLM density).val.1 target -
        (Complex.I / 2) * ∫ source in (target - Real.pi)..(target + Real.pi), density.val.1 source := by
  have conjugate := circleCauchyCLM_conjugate density target
  have integral_conjugate :
      (∫ source in (target - Real.pi)..(target + Real.pi), star (density.val.1 source)) =
      star (∫ source in (target - Real.pi)..(target + Real.pi), density.val.1 source) :=
    Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm
      (density.val.1.continuous.intervalIntegrable _ _)
  rw [integral_conjugate] at conjugate
  have star_identity := congrArg (fun value : ℂ => star value) conjugate
  simp only [Complex.star_def, map_sub, map_mul, Complex.conj_I, Complex.conj_conj] at star_identity
  change star ((circleCauchyCLM (holderConjugate density)).val.1 target) =
    (circleCauchyCLM density).val.1 target - -Complex.I *
      (∫ source in (target - Real.pi)..(target + Real.pi), density.val.1 source) at star_identity
  have hilbert := periodicHilbertCLM_value density target
  change (periodicHilbertCLM density).val.1 target = (1 / (2 * Real.pi)) •
    ((circleCauchyCLM density).val.1 target + star ((circleCauchyCLM (holderConjugate density)).val.1 target)) at hilbert
  rw [star_identity, Complex.real_smul] at hilbert
  push_cast at hilbert
  field_simp [Real.pi_ne_zero] at hilbert
  linear_combination -(1 / 2 : ℂ) * hilbert

end

end EulerNonuniqueness.Paper
