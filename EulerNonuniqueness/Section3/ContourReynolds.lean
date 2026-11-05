import EulerNonuniqueness.Section3.ContourReynoldsVariation

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem hasDerivAt_materialRadialFlux
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position)
    (curve tangent velocity mixed : ℝ → ℝ → ℂ)
    (curve_continuous : Continuous (Function.uncurry curve))
    (tangent_continuous : Continuous (Function.uncurry tangent))
    (velocity_continuous : Continuous (Function.uncurry velocity))
    (mixed_continuous : Continuous (Function.uncurry mixed))
    (time radius : ℝ) (radius_positive : 0 < radius)
    (curve_time_derivative : ∀ parameter ∈ Metric.ball time radius, ∀ label,
      HasDerivAt (fun parameter => curve parameter label) (velocity parameter label) parameter)
    (tangent_time_derivative : ∀ parameter ∈ Metric.ball time radius, ∀ label,
      HasDerivAt (fun parameter => tangent parameter label) (mixed parameter label) parameter)
    (lower upper : ℝ)
    (curve_label_derivative : ∀ label, HasDerivAt (curve time) (tangent time label) label)
    (velocity_label_derivative : ∀ label, HasDerivAt (velocity time) (mixed time label) label)
    (closed_curve : curve time upper = curve time lower)
    (closed_velocity : velocity time upper = velocity time lower) :
    HasDerivAt (fun parameter => ∫ label in lower..upper, ∫ scale in (0 : ℝ)..1,
      scale * function (scale • curve parameter label) * contourAreaPair (curve parameter label) (tangent parameter label))
      (∫ label in lower..upper,
        function (curve time label) * contourAreaPair (velocity time label) (tangent time label)) time := by
  let integrand : (ℝ × ℝ) → ℝ → ℝ := fun pair scale =>
    scale * function (scale • curve pair.1 pair.2) * contourAreaPair (curve pair.1 pair.2) (tangent pair.1 pair.2)
  let variation : (ℝ × ℝ) → ℝ → ℝ := fun pair scale =>
    contourReynoldsVariation function derivative (curve pair.1) (tangent pair.1)
      (velocity pair.1) (mixed pair.1) pair.2 scale
  have integrand_continuous : Continuous (Function.uncurry integrand) := by
    dsimp [integrand, Function.uncurry, contourAreaPair]
    fun_prop
  have variation_continuous : Continuous (Function.uncurry variation) := by
    dsimp [variation, contourReynoldsVariation, Function.uncurry, contourAreaPair]
    fun_prop
  have inner_integral_continuous : Continuous (fun pair => ∫ scale in (0 : ℝ)..1, integrand pair scale) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
      integrand_continuous continuous_const
  have inner_variation_continuous : Continuous (fun pair => ∫ scale in (0 : ℝ)..1, variation pair scale) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume)
      variation_continuous continuous_const
  have inner_derivative (parameter : ℝ) (parameter_mem : parameter ∈ Metric.ball time (radius / 2)) (label : ℝ) :
      HasDerivAt (fun parameter => ∫ scale in (0 : ℝ)..1, integrand (parameter, label) scale)
        (∫ scale in (0 : ℝ)..1, variation (parameter, label) scale) parameter := by
    apply hasDerivAt_intervalIntegral_of_joint_continuous
      (fun parameter scale => integrand (parameter, label) scale)
      (fun parameter scale => variation (parameter, label) scale)
      parameter 0 1 (radius / 2) (by positivity)
    · exact integrand_continuous.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)
    · exact variation_continuous.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)
    · intro scale _ current current_mem
      have current_inside : current ∈ Metric.ball time radius := by
        have triangle := dist_triangle current parameter time
        have first : dist current parameter < radius / 2 := current_mem
        have second : dist parameter time < radius / 2 := parameter_mem
        change dist current time < radius
        linarith
      exact hasDerivAt_contourReynolds_time function derivative function_derivative
        (curve_time_derivative current current_inside label) (tangent_time_derivative current current_inside label) scale
  have outer_derivative := hasDerivAt_intervalIntegral_of_joint_continuous
    (fun parameter label => ∫ scale in (0 : ℝ)..1, integrand (parameter, label) scale)
    (fun parameter label => ∫ scale in (0 : ℝ)..1, variation (parameter, label) scale)
    time lower upper (radius / 2) (by positivity) inner_integral_continuous inner_variation_continuous
    (fun label _ parameter inside => inner_derivative parameter inside label)
  have variation_identity := integral_contourReynolds_variation function derivative
    function_continuous derivative_continuous function_derivative
    (curve time) (tangent time) (velocity time) (mixed time)
    (curve_continuous.comp (continuous_const.prodMk continuous_id))
    (tangent_continuous.comp (continuous_const.prodMk continuous_id))
    (velocity_continuous.comp (continuous_const.prodMk continuous_id))
    (mixed_continuous.comp (continuous_const.prodMk continuous_id))
    curve_label_derivative velocity_label_derivative lower upper closed_curve closed_velocity
  change HasDerivAt (fun parameter => ∫ label in lower..upper, ∫ scale in (0 : ℝ)..1,
    scale * function (scale • curve parameter label) * contourAreaPair (curve parameter label) (tangent parameter label))
    (∫ label in lower..upper, ∫ scale in (0 : ℝ)..1,
      contourReynoldsVariation function derivative (curve time) (tangent time)
        (velocity time) (mixed time) label scale) time at outer_derivative
  rw [variation_identity] at outer_derivative
  exact outer_derivative

end

end EulerNonuniqueness.Paper
