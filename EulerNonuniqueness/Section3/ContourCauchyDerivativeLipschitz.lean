import EulerNonuniqueness.Section3.ContourCauchyFrechet
import EulerNonuniqueness.Section3.CauchyDerivativeDifference
import EulerNonuniqueness.Section3.ComplexHolderInstances

open Set Metric Filter
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance cauchyDerivativeLipschitzHolderComplexSpace : NormedSpace ℂ PeriodicHolderHalf :=
  Submodule.normedSpace complexPeriodicHolderGraph

local instance cauchyDerivativeLipschitzC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf :=
  Submodule.normedSpace complexPeriodicC1HolderGraph

local instance cauchyDerivativeLipschitzComplexOperatorGroup : SeminormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

local instance cauchyDerivativeLipschitzHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph

local instance cauchyDerivativeLipschitzC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

local instance cauchyDerivativeLipschitzRealOperatorGroup : SeminormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem contourCauchyDirectionalDerivative_difference_bound
    (first second direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (nonnegative : 0 ≤ radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    {parameterRadius : ℝ≥0} (positive : 0 < parameterRadius)
    (first_nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
      ‖first + parameter • direction - standardCircleBanach‖ ≤ radius)
    (second_nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
      ‖second + parameter • direction - standardCircleBanach‖ ≤ radius) :
    ‖contourCauchyDirectionalDerivative first direction density -
      contourCauchyDirectionalDerivative second direction density‖ ≤
      (contourCauchyParameterOperatorConstant radius * ‖first - second‖ * ‖density‖) /
        (parameterRadius : ℝ) := by
  have holomorphic (data : PeriodicC1HolderHalf)
      (nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
        ‖data + parameter • direction - standardCircleBanach‖ ≤ radius) :
      DiffContOnCl ℂ
        (fun current : ℂ => extendedContourCauchy (data + current • direction) density)
        (ball 0 parameterRadius) := by
    apply DiffContOnCl.mk_ball _
      (extendedContourCauchy_continuousOn_complex_line data direction density
        nonnegative small nearby)
    intro current member
    exact (extendedContourCauchy_differentiableAt_complex_line data direction density current
      ((nearby current (ball_subset_closedBall member)).trans_lt small)).differentiableWithinAt
  apply cauchy_derivative_difference_bound positive
    (holomorphic first first_nearby) (holomorphic second second_nearby)
  intro parameter member
  rw [extendedContourCauchy_eq _ _
    ((first_nearby parameter (sphere_subset_closedBall member)).trans_lt small),
    extendedContourCauchy_eq _ _
    ((second_nearby parameter (sphere_subset_closedBall member)).trans_lt small)]
  have estimate := contourCauchyOperator_parameter_norm_bound
    (first + parameter • direction) (second + parameter • direction) density
    nonnegative small (first_nearby parameter (sphere_subset_closedBall member))
    (second_nearby parameter (sphere_subset_closedBall member))
  have difference : first + parameter • direction - (second + parameter • direction) =
      first - second := by abel
  simpa only [difference] using estimate

theorem contourCauchyDerivativeCLM_local_difference_bound
    (first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (inner_nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ innerRadius)
    (second_near : ‖second - standardCircleBanach‖ ≤ innerRadius) :
    ‖contourCauchyDerivativeCLM first density (first_near.trans_lt gap) small -
      contourCauchyDerivativeCLM second density (second_near.trans_lt gap) small‖ ≤
      (contourCauchyParameterOperatorConstant outerRadius * ‖first - second‖ * ‖density‖) /
        (outerRadius - innerRadius) := by
  let difference := contourCauchyDerivativeCLM first density (first_near.trans_lt gap) small -
    contourCauchyDerivativeCLM second density (second_near.trans_lt gap) small
  have outer_nonnegative : 0 ≤ outerRadius := inner_nonnegative.trans gap.le
  have constant_nonnegative : 0 ≤ contourCauchyParameterOperatorConstant outerRadius :=
    (contourCauchyParameterSupConstant_nonneg outer_nonnegative small).trans (le_max_left _ _)
  have real_estimate : ‖difference.restrictScalars ℝ‖ ≤
      (contourCauchyParameterOperatorConstant outerRadius * ‖first - second‖ * ‖density‖) /
        (outerRadius - innerRadius) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm
      (div_nonneg (mul_nonneg (mul_nonneg constant_nonnegative (norm_nonneg _))
        (norm_nonneg _)) (sub_nonneg.mpr gap.le))
    intro direction unit
    let parameterRadius : ℝ≥0 := ⟨outerRadius - innerRadius, sub_nonneg.mpr gap.le⟩
    have positive : 0 < parameterRadius := sub_pos.mpr gap
    have nearby (data : PeriodicC1HolderHalf)
        (near : ‖data - standardCircleBanach‖ ≤ innerRadius)
        (parameter : ℂ) (member : parameter ∈ closedBall (0 : ℂ) parameterRadius) :
        ‖data + parameter • direction - standardCircleBanach‖ ≤ outerRadius := by
      have parameter_bound : ‖parameter‖ ≤ outerRadius - innerRadius := by
        simpa only [mem_closedBall, dist_zero_right] using member
      have estimate := complexContourPerturbation_distance data direction parameter
      rw [unit, mul_one] at estimate
      exact estimate.trans (by linarith)
    exact contourCauchyDirectionalDerivative_difference_bound first second direction density
      outer_nonnegative small positive (nearby first first_near) (nearby second second_near)
  simpa only [ContinuousLinearMap.norm_restrictScalars] using real_estimate

end

end EulerNonuniqueness.Paper
