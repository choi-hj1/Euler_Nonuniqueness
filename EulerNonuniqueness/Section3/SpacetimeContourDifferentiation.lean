import EulerNonuniqueness.Section3.SpacetimeContourVariation
import EulerNonuniqueness.Section3.NestedParameterDifferentiation

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem hasDerivAt_spacetimeMaterialRadialIntegral
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ point, HasFDerivAt function (derivative point) point)
    (curve tangent velocity mixed : ℝ → ℝ → ℂ)
    (curve_continuous : Continuous (Function.uncurry curve))
    (tangent_continuous : Continuous (Function.uncurry tangent))
    (velocity_continuous : Continuous (Function.uncurry velocity))
    (mixed_continuous : Continuous (Function.uncurry mixed))
    (time radius lower upper : ℝ) (radius_positive : 0 < radius)
    (curve_derivative : ∀ parameter ∈ Metric.ball time radius, ∀ label,
      HasDerivAt (fun parameter => curve parameter label) (velocity parameter label) parameter)
    (tangent_derivative : ∀ parameter ∈ Metric.ball time radius, ∀ label,
      HasDerivAt (fun parameter => tangent parameter label) (mixed parameter label) parameter) :
    HasDerivAt (fun parameter => ∫ label in lower..upper, ∫ scale in (0 : ℝ)..1,
      scale * function (parameter, scale • curve parameter label) *
        contourAreaPair (curve parameter label) (tangent parameter label))
      (∫ label in lower..upper, ∫ scale in (0 : ℝ)..1,
        scale * (derivative (time, scale • curve time label) (1, scale • velocity time label) *
          contourAreaPair (curve time label) (tangent time label) +
          function (time, scale • curve time label) *
            (contourAreaPair (velocity time label) (tangent time label) +
              contourAreaPair (curve time label) (mixed time label)))) time := by
  refine hasDerivAt_nested_intervalIntegral_of_joint_continuous
    (fun parameter label scale => scale * function (parameter, scale • curve parameter label) *
      contourAreaPair (curve parameter label) (tangent parameter label))
    (fun parameter label scale =>
      scale * (derivative (parameter, scale • curve parameter label) (1, scale • velocity parameter label) *
        contourAreaPair (curve parameter label) (tangent parameter label) +
        function (parameter, scale • curve parameter label) *
          (contourAreaPair (velocity parameter label) (tangent parameter label) +
            contourAreaPair (curve parameter label) (mixed parameter label))))
    ?_ ?_ time radius lower upper 0 1 radius_positive ?_
  · dsimp only [contourAreaPair, Function.uncurry]
    fun_prop
  · dsimp only [contourAreaPair, Function.uncurry]
    fun_prop
  · intro parameter member label _ scale _
    exact hasDerivAt_spacetimeContourReynolds_time function derivative function_derivative
      (curve_derivative parameter member label) (tangent_derivative parameter member label) scale

end

end EulerNonuniqueness.Paper
