import EulerNonuniqueness.Section3.ContourVelocityAmbientDerivative
import EulerNonuniqueness.Section3.ContourQuadraticHomogeneity

open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourVelocityAmbientQuadratic (data increment : PeriodicC1HolderHalf) : C1HolderGraphAmbient :=
  ((contourVelocityHolderQuadratic data increment).val.1, contourVelocityTangentQuadratic data increment)

def contourVelocityValueCubicBound (data : PeriodicC1HolderHalf) (radius : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) *
    (16 * (contourCauchyUniformOperatorConstant radius * ‖holderConjugate (c1ValueHolder data)‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 3 +
      16 * contourCauchyUniformOperatorConstant radius / (radius - ‖data - standardCircleBanach‖) ^ 2)

def contourVelocityTangentCubicBound (innerRadius outerRadius : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) *
    (2 * (outerRadius + 2) * contourTangentInnerCubicBound innerRadius outerRadius +
      2 * contourTangentInnerQuadraticBound innerRadius outerRadius)

def contourVelocityAmbientCubicBound (data : PeriodicC1HolderHalf) (innerRadius outerRadius : ℝ) : ℝ :=
  max (contourVelocityValueCubicBound data outerRadius)
    (contourVelocityTangentCubicBound innerRadius outerRadius)

theorem contourVelocityAmbientQuadratic_real_smul (data increment : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourVelocityAmbientQuadratic data (scalar • increment) =
      scalar ^ 2 • contourVelocityAmbientQuadratic data increment := by
  unfold contourVelocityAmbientQuadratic
  rw [contourVelocityHolderQuadratic_real_smul data increment small,
    contourVelocityTangentQuadratic_real_smul data increment small]
  rfl

theorem contourVelocityAmbient_cubic_taylor_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius)
    (increment_small : ‖increment‖ ≤ (outerRadius - innerRadius) / 4)
    (inverse_small : ‖increment‖ ≤ (1 - outerRadius) / 2) (increment_bound : ‖increment‖ ≤ 1) :
    ‖(extendedContourVelocity (data + increment)).val - (extendedContourVelocity data).val -
      contourVelocityAmbientDerivativeCLM data (nearby.trans_lt gap) small increment -
      contourVelocityAmbientQuadratic data increment‖ ≤
      contourVelocityAmbientCubicBound data innerRadius outerRadius * ‖increment‖ ^ 3 := by
  have outer_near := nearby.trans_lt gap
  have next_nearby : ‖data + increment - standardCircleBanach‖ ≤ outerRadius := by
    have identity : data + increment - standardCircleBanach =
        (data - standardCircleBanach) + increment := by abel
    rw [identity]
    exact (norm_add_le (data - standardCircleBanach) increment).trans (by linarith)
  have value_bound :
      ‖holderContourVelocity (data + increment) - holderContourVelocity data -
        contourVelocityHolderDerivativeCLM data outer_near small increment -
        contourVelocityHolderQuadratic data increment‖ ≤
      contourVelocityValueCubicBound data outerRadius * ‖increment‖ ^ 3 :=
    contourVelocityHolder_cubic_taylor_bound data increment outer_near small
      (increment_small.trans (by linarith))
  have tangent_bound :
      ‖holderContourVelocityTangent (data + increment) - holderContourVelocityTangent data -
        contourVelocityTangentDerivativeCLM data outer_near small increment -
        contourVelocityTangentQuadratic data increment‖ ≤
      contourVelocityTangentCubicBound innerRadius outerRadius * ‖increment‖ ^ 3 := by
    rw [← contourVelocityTangentLinear_eq_derivative data increment outer_near small]
    exact contourVelocityTangent_cubic_uniform_bound data increment nonnegative gap small nearby
      increment_small inverse_small increment_bound
  have value_projection :
      ‖(holderContourVelocity (data + increment) - holderContourVelocity data -
        contourVelocityHolderDerivativeCLM data outer_near small increment -
        contourVelocityHolderQuadratic data increment).val.1‖ ≤
      ‖holderContourVelocity (data + increment) - holderContourVelocity data -
        contourVelocityHolderDerivativeCLM data outer_near small increment -
        contourVelocityHolderQuadratic data increment‖ :=
    norm_fst_le (holderContourVelocity (data + increment) - holderContourVelocity data -
      contourVelocityHolderDerivativeCLM data outer_near small increment -
      contourVelocityHolderQuadratic data increment).val
  rw [extendedContourVelocity_ambient_eq (data + increment) (next_nearby.trans_lt small),
    extendedContourVelocity_ambient_eq data (outer_near.trans small)]
  change max
    ‖(holderContourVelocity (data + increment) - holderContourVelocity data -
      contourVelocityHolderDerivativeCLM data outer_near small increment -
      contourVelocityHolderQuadratic data increment).val.1‖
    ‖holderContourVelocityTangent (data + increment) - holderContourVelocityTangent data -
      contourVelocityTangentDerivativeCLM data outer_near small increment -
      contourVelocityTangentQuadratic data increment‖ ≤ _
  exact max_le
    ((value_projection.trans value_bound).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    (tangent_bound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))

end

end EulerNonuniqueness.Paper
