import EulerNonuniqueness.General.PeriodicGeneratorVariation

namespace EulerNonuniqueness.General

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

variable (family : ℝ → ℝ → Space →L[ℝ] Space) (operator : ℝ → Space →L[ℝ] Space)
  (variation : Space →L[ℝ] Space) {period : ℝ} (periodPositive : 0 < period)
  (jointContinuous : Continuous (fun pair : ℝ × ℝ => family pair.1 pair.2))
  (atZero : ∀ parameter, family parameter 0 = ContinuousLinearMap.id ℝ Space)
  (addition : ∀ parameter first second,
    family parameter (first + second) = (family parameter first).comp (family parameter second))
  (timeDerivative : ∀ parameter time,
    HasDerivAt (family parameter) ((operator parameter).comp (family parameter time)) time)
  (operatorDerivative : HasDerivAt operator variation 0)
  (periodic : ∀ᶠ parameter in 𝓝 (0 : ℝ), family parameter period = ContinuousLinearMap.id ℝ Space)

include periodPositive jointContinuous atZero addition timeDerivative operatorDerivative periodic

theorem periodicGeneratorVariation_conjugate_integral_zero (initial : Space) :
    (∫ time in (0 : ℝ)..period,
      family 0 (-time) (variation (family 0 time initial))) = 0 := by
  have actual := periodicGeneratorVariation_integral_zero family operator variation periodPositive
    jointContinuous atZero addition timeDerivative operatorDerivative periodic initial
  have shifted (time : ℝ) : family 0 (period - time) = family 0 (-time) := by
    rw [sub_eq_add_neg, addition, periodic.self_of_nhds, ContinuousLinearMap.id_comp]
  simpa only [shifted] using actual

theorem periodicGeneratorVariation_operator_average_zero :
    (∫ time in (0 : ℝ)..period,
      (family 0 (-time)).comp (variation.comp (family 0 time))) = 0 := by
  have slice : Continuous (family 0) := jointContinuous.comp (continuous_const.prodMk continuous_id)
  have integrable : IntervalIntegrable
      (fun time => (family 0 (-time)).comp (variation.comp (family 0 time))) volume 0 period :=
    ((slice.comp continuous_neg).clm_comp (continuous_const.clm_comp slice)).intervalIntegrable _ _
  apply ContinuousLinearMap.ext
  intro initial
  have commutation :
      (∫ time in (0 : ℝ)..period, family 0 (-time) (variation (family 0 time initial))) =
      (∫ time in (0 : ℝ)..period, (family 0 (-time)).comp (variation.comp (family 0 time))) initial :=
    (ContinuousLinearMap.apply ℝ Space initial).intervalIntegral_comp_comm integrable
  change (∫ time in (0 : ℝ)..period,
    (family 0 (-time)).comp (variation.comp (family 0 time))) initial = 0
  rw [← commutation]
  exact periodicGeneratorVariation_conjugate_integral_zero family operator variation periodPositive
    jointContinuous atZero addition timeDerivative operatorDerivative periodic initial

end

end EulerNonuniqueness.General
