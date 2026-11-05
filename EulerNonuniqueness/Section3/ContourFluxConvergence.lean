import EulerNonuniqueness.Section3.ContourBiotSavartAdvection

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

theorem tendsto_intervalIntegral_contourFlux
    (curve tangent : ℝ → ℂ) (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (function : ℂ → ℝ) (function_continuous : Continuous function)
    (fields : ℕ → ℂ → ℂ) (limit : ℂ → ℂ) (field_continuous : ∀ index, Continuous (fields index))
    (pointwise : ∀ position, Tendsto (fun index => fields index position) atTop (𝓝 (limit position)))
    (bound : ℝ) (bounded : ∀ index position, ‖fields index position‖ ≤ bound) (lower upper : ℝ) :
    Tendsto (fun index => ∫ label in lower..upper,
      function (curve label) * contourAreaPair (fields index (curve label)) (tangent label)) atTop
      (𝓝 (∫ label in lower..upper,
        function (curve label) * contourAreaPair (limit (curve label)) (tangent label))) := by
  have restricted : Tendsto
      (fun index => ∫ label in uIoc lower upper, function (curve label) *
        contourAreaPair (fields index (curve label)) (tangent label)) atTop
      (𝓝 (∫ label in uIoc lower upper, function (curve label) *
        contourAreaPair (limit (curve label)) (tangent label))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun label => ‖function (curve label)‖ * (bound * ‖tangent label‖))
    · intro index
      exact ((function_continuous.comp curve_continuous).mul
        (continuous_contourAreaPair.comp (((field_continuous index).comp curve_continuous).prodMk
          tangent_continuous))).aestronglyMeasurable
    · have continuous_bound : Continuous (fun label => ‖function (curve label)‖ * (bound * ‖tangent label‖)) :=
        (function_continuous.comp curve_continuous).norm.mul (continuous_const.mul tangent_continuous.norm)
      exact (continuous_bound.intervalIntegrable lower upper).def'
    · intro index
      exact Eventually.of_forall fun label => by
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (norm_contourAreaPair_le _ _).trans
          (mul_le_mul_of_nonneg_right (bounded index _) (norm_nonneg _))
    · exact Eventually.of_forall fun label =>
        ((continuous_contourAreaPair.tendsto _).comp
          ((pointwise (curve label)).prodMk_nhds tendsto_const_nhds)).const_mul _
  simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc] using
    restricted.const_smul (if lower ≤ upper then (1 : ℝ) else -1)

end

end EulerNonuniqueness.Paper
