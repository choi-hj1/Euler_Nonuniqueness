import EulerNonuniqueness.Section3.ContourKernelVariation

open Set MeasureTheory Filter

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem measurable_contourCauchyKernelVariation (data direction : PeriodicC1HolderHalf) (target : ℝ) :
    Measurable (contourCauchyKernelVariation data direction target) := by
  have denominator : Measurable (fun source => data.val.1 target - data.val.1 source) :=
    measurable_const.sub data.val.1.continuous.measurable
  exact (direction.val.2.val.1.continuous.measurable.div denominator).sub
    ((data.val.2.val.1.continuous.measurable.mul
      (measurable_const.sub direction.val.1.continuous.measurable)).div (denominator.pow_const 2))

theorem contourCauchyKernelVariation_majorized (data direction : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ)
    {source : ℝ} (inside : source ∈ Icc (target - Real.pi) (target + Real.pi)) :
    ‖contourCauchyKernelVariation data direction target source‖ ≤
      (2 * ‖data‖ * ‖direction‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) ^ 2) *
        inverseSqrtDistance target source := by
  by_cases equal : source = target
  · subst source
    simp [contourCauchyKernelVariation, inverseSqrtDistance]
  · have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [inside.1, inside.2, Real.pi_pos]
    have result := contourCauchyKernelVariation_weak_bound data direction equal (sub_pos.mpr small)
      (by simpa only [abs_sub_comm target source] using PeriodicC1HolderHalf.chord_bound_extended data nearby)
    exact result.trans_eq (by simp only [inverseSqrtDistance, abs_sub_comm target source, div_eq_mul_inv, mul_inv]; ring)

theorem contourCauchyKernelVariation_intervalIntegrable (data direction : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    IntervalIntegrable (contourCauchyKernelVariation data direction target) volume
      (target - Real.pi) (target + Real.pi) := by
  have integrable := weakSingular_integrable
    ((measurable_contourCauchyKernelVariation data direction target).aestronglyMeasurable.restrict)
    (fun source inside => contourCauchyKernelVariation_majorized data direction small target inside)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mpr integrable

def contourCauchyVariationIntegral (data direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (target : ℝ) : ℂ :=
  ∫ source in (target - Real.pi)..(target + Real.pi),
    contourCauchyKernelVariation data direction target source * density.val.1 source

theorem contourCauchyVariationIntegral_integrable (data direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    IntervalIntegrable (fun source => contourCauchyKernelVariation data direction target source * density.val.1 source)
      volume (target - Real.pi) (target + Real.pi) := by
  have bound := weakSingular_integrable
    (((measurable_contourCauchyKernelVariation data direction target).mul
      density.val.1.continuous.measurable).aestronglyMeasurable.restrict)
    (bound := (2 * ‖data‖ * ‖direction‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) ^ 2) * ‖density‖)
    (fun source inside => by
      rw [norm_mul]
      have estimate := mul_le_mul (contourCauchyKernelVariation_majorized data direction small target inside)
        (PeriodicHolderHalf.value_bound density source) (norm_nonneg _) (by unfold inverseSqrtDistance; positivity)
      exact estimate.trans_eq (by ring))
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mpr bound

end

end EulerNonuniqueness.Paper
