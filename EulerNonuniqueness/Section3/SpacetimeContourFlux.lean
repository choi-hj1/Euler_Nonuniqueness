import EulerNonuniqueness.Section3.SpacetimeContourDifferentiation

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem nested_intervalIntegral_add_continuous (first second : ℝ → ℝ → ℝ)
    (first_continuous : Continuous (Function.uncurry first))
    (second_continuous : Continuous (Function.uncurry second)) (lower upper : ℝ) :
    (∫ label in lower..upper, ∫ scale in (0 : ℝ)..1, first label scale + second label scale) =
      (∫ label in lower..upper, ∫ scale in (0 : ℝ)..1, first label scale) +
        ∫ label in lower..upper, ∫ scale in (0 : ℝ)..1, second label scale := by
  have first_inner : Continuous (fun label => ∫ scale in (0 : ℝ)..1, first label scale) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) first_continuous continuous_const
  have second_inner : Continuous (fun label => ∫ scale in (0 : ℝ)..1, second label scale) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := volume) second_continuous continuous_const
  rw [← intervalIntegral.integral_add (first_inner.intervalIntegrable lower upper)
    (second_inner.intervalIntegrable lower upper)]
  apply intervalIntegral.integral_congr
  intro label _
  exact intervalIntegral.integral_add
    ((first_continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
    ((second_continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)

theorem integral_spacetimeContourReynolds_variation
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ point, HasFDerivAt function (derivative point) point)
    (time : ℝ) (curve tangent velocity mixed : ℝ → ℂ)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (velocity_continuous : Continuous velocity) (mixed_continuous : Continuous mixed)
    (curve_derivative : ∀ label, HasDerivAt curve (tangent label) label)
    (velocity_derivative : ∀ label, HasDerivAt velocity (mixed label) label)
    (lower upper : ℝ) (closed_curve : curve upper = curve lower)
    (closed_velocity : velocity upper = velocity lower) :
    (∫ label in lower..upper, ∫ scale in (0 : ℝ)..1,
      scale * (derivative (time, scale • curve label) (1, scale • velocity label) *
        contourAreaPair (curve label) (tangent label) +
        function (time, scale • curve label) * (contourAreaPair (velocity label) (tangent label) +
          contourAreaPair (curve label) (mixed label)))) =
      (∫ label in lower..upper, ∫ scale in (0 : ℝ)..1,
        scale * derivative (time, scale • curve label) (1, 0) * contourAreaPair (curve label) (tangent label)) +
      ∫ label in lower..upper, function (time, curve label) * contourAreaPair (velocity label) (tangent label) := by
  let spatial : ℂ → ℂ →L[ℝ] ℝ := fun position =>
    (derivative (time, position)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)
  let temporal : ℝ → ℝ → ℝ := fun label scale =>
    scale * derivative (time, scale • curve label) (1, 0) * contourAreaPair (curve label) (tangent label)
  let spatial_variation := contourReynoldsVariation (fun position => function (time, position))
    spatial curve tangent velocity mixed
  have temporal_continuous : Continuous (Function.uncurry temporal) := by
    dsimp [temporal, Function.uncurry, contourAreaPair]
    fun_prop
  have spatial_continuous : Continuous spatial := by
    exact (derivative_continuous.comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  have spatial_variation_continuous : Continuous (Function.uncurry spatial_variation) := by
    change Continuous (fun pair : ℝ × ℝ =>
      pair.2 * (spatial (pair.2 • curve pair.1) (pair.2 • velocity pair.1) *
        (star (curve pair.1) * tangent pair.1).im +
        function (time, pair.2 • curve pair.1) *
          ((star (velocity pair.1) * tangent pair.1).im + (star (curve pair.1) * mixed pair.1).im)))
    fun_prop
  have integrand_identity : ∀ label scale,
      scale * (derivative (time, scale • curve label) (1, scale • velocity label) *
        contourAreaPair (curve label) (tangent label) +
        function (time, scale • curve label) * (contourAreaPair (velocity label) (tangent label) +
          contourAreaPair (curve label) (mixed label))) = temporal label scale + spatial_variation label scale := by
    intro label scale
    rw [spacetimeContourReynolds_derivative_split]
    dsimp [temporal, spatial_variation, contourReynoldsVariation, spatial]
    ring
  simp_rw [integrand_identity]
  rw [nested_intervalIntegral_add_continuous temporal spatial_variation temporal_continuous
    spatial_variation_continuous lower upper]
  congr 1
  exact integral_contourReynolds_variation (fun position => function (time, position)) spatial
    (function_continuous.comp (continuous_const.prodMk continuous_id)) spatial_continuous
    (fun position => (function_derivative _).comp position (hasFDerivAt_prodMk_right time position))
    curve tangent velocity mixed curve_continuous tangent_continuous velocity_continuous mixed_continuous
    curve_derivative velocity_derivative lower upper closed_curve closed_velocity

end

end EulerNonuniqueness.Paper
