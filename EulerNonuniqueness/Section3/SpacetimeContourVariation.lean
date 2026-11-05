import EulerNonuniqueness.Section3.ContourReynolds
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace EulerNonuniqueness.Paper

noncomputable section

theorem hasDerivAt_spacetimeContourReynolds_time
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_derivative : ∀ point, HasFDerivAt function (derivative point) point)
    {curve tangent : ℝ → ℂ} {velocity mixed : ℂ} {time : ℝ}
    (curve_derivative : HasDerivAt curve velocity time)
    (tangent_derivative : HasDerivAt tangent mixed time) (scale : ℝ) :
    HasDerivAt (fun parameter => scale * function (parameter, scale • curve parameter) *
      contourAreaPair (curve parameter) (tangent parameter))
      (scale * (derivative (time, scale • curve time) (1, scale • velocity) *
        contourAreaPair (curve time) (tangent time) +
        function (time, scale • curve time) * (contourAreaPair velocity (tangent time) +
          contourAreaPair (curve time) mixed))) time := by
  have path_derivative := (hasDerivAt_id time).prodMk (curve_derivative.const_smul scale)
  have scalar_derivative := (function_derivative _).comp_hasDerivAt time path_derivative
  have area_derivative := hasDerivAt_contourAreaPair curve_derivative tangent_derivative
  convert (scalar_derivative.const_mul scale).mul area_derivative using 1 <;>
    simp only [Function.comp_apply, id_eq] <;> ring

theorem spacetimeContourReynolds_derivative_split
    (linear : (ℝ × ℂ) →L[ℝ] ℝ) (velocity : ℂ) :
    linear (1, velocity) = linear (1, 0) + linear (0, velocity) := by
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

end

end EulerNonuniqueness.Paper
