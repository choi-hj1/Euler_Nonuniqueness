import EulerNonuniqueness.Section6.MovingPatchFieldBounds
import EulerNonuniqueness.Section6.KernelReceiverTaylor

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

def biotSavartKernelStrain (center source : ℂ) : ℂ :=
  -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) / star (center - source) ^ 2

theorem norm_biotSavartKernelStrain (center source : ℂ) :
    ‖biotSavartKernelStrain center source‖ = 1 / (2 * Real.pi * ‖center - source‖ ^ 2) := by
  rw [biotSavartKernelStrain, norm_div, norm_neg, norm_div, norm_pow, norm_star,
    Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  ring

theorem integrableOn_biotSavartKernelStrain_of_separation {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤)
    {center : ℂ} {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ domain, distance ≤ ‖center - source‖) :
    IntegrableOn (biotSavartKernelStrain center) domain := by
  have majorant : IntegrableOn (fun _ : ℂ => 1 / (2 * Real.pi * distance ^ 2)) domain :=
    integrableOn_const.mpr (Or.inr finite)
  have measurableKernel : Measurable (biotSavartKernelStrain center) := by
    unfold biotSavartKernelStrain
    fun_prop
  apply majorant.mono' measurableKernel.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurable] with source member
  rw [norm_biotSavartKernelStrain]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ positive.le (separated source member) 2) (by positivity))

theorem indicator_biotSavart_strain_taylor_bound {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤) (density : ℝ)
    {center position : ℂ} {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ domain, distance ≤ ‖center - source‖)
    (near : 2 * ‖position - center‖ ≤ distance) :
    ‖biotSavart (domain.indicator (fun _ => density)) position -
        biotSavart (domain.indicator (fun _ => density)) center -
        (density • ∫ source in domain, biotSavartKernelStrain center source) * star (position - center)‖ ≤
      |density| * volume.real domain * ‖position - center‖ ^ 2 / (Real.pi * distance ^ 3) := by
  have positionSeparated (source : ℂ) (member : source ∈ domain) : distance / 2 ≤ ‖position - source‖ := by
    have triangle := norm_add_le (center - position) (position - source)
    rw [sub_add_sub_cancel, norm_sub_rev center position] at triangle
    linarith [separated source member]
  have positionIntegrable := integrableOn_biotSavartKernel_of_separation measurable finite
    (by positivity : 0 < distance / 2) positionSeparated
  have centerIntegrable := integrableOn_biotSavartKernel_of_separation measurable finite positive separated
  have strainIntegrable := integrableOn_biotSavartKernelStrain_of_separation measurable finite positive separated
  have linearIntegrable := strainIntegrable.mul_const (star (position - center))
  have identity (source : ℂ) :
      biotSavartKernel (position - source) - biotSavartKernel (center - source) -
          biotSavartKernelStrain center source * star (position - center) =
      biotSavartKernel (position - source) - biotSavartKernel (center - source) +
        (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
          starRingEnd ℂ ((position - center) / (center - source) ^ 2) := by
    simp only [biotSavartKernelStrain, map_div₀, map_pow, starRingEnd_apply]
    ring
  have estimate := norm_integral_le_of_norm_le (μ := volume.restrict domain)
    (f := fun source => biotSavartKernel (position - source) - biotSavartKernel (center - source) -
      biotSavartKernelStrain center source * star (position - center))
    (g := fun _ : ℂ => ‖position - center‖ ^ 2 / (Real.pi * distance ^ 3))
    (integrableOn_const.mpr (Or.inr finite)) (by
      filter_upwards [ae_restrict_mem measurable] with source member
      rw [identity]
      exact biotSavart_receiver_taylor_bound positive (separated source member) near)
  have expansion :
      (∫ source in domain, biotSavartKernel (position - source) - biotSavartKernel (center - source) -
        biotSavartKernelStrain center source * star (position - center)) =
      (∫ source in domain, biotSavartKernel (position - source)) -
        (∫ source in domain, biotSavartKernel (center - source)) -
        (∫ source in domain, biotSavartKernelStrain center source) * star (position - center) := by
    calc
      _ = (∫ source in domain, biotSavartKernel (position - source) - biotSavartKernel (center - source)) -
          (∫ source in domain, biotSavartKernelStrain center source * star (position - center)) :=
        integral_sub (positionIntegrable.sub centerIntegrable) linearIntegrable
      _ = _ := by rw [integral_sub positionIntegrable centerIntegrable, integral_mul_const]
  rw [expansion, integral_const] at estimate
  rw [biotSavart_indicator_density_integral measurable, biotSavart_indicator_density_integral measurable]
  have factor :
      density • (∫ source in domain, biotSavartKernel (position - source)) -
        density • (∫ source in domain, biotSavartKernel (center - source)) -
        (density • ∫ source in domain, biotSavartKernelStrain center source) * star (position - center) =
      density • ((∫ source in domain, biotSavartKernel (position - source)) -
        (∫ source in domain, biotSavartKernel (center - source)) -
        (∫ source in domain, biotSavartKernelStrain center source) * star (position - center)) := by
    simp only [Complex.real_smul]
    ring
  rw [factor, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left estimate (abs_nonneg density)).trans_eq (by
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    ring)

end EulerNonuniqueness.Section6
