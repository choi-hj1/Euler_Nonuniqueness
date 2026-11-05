import EulerNonuniqueness.Section3.ContourDerivativeLineHolomorphic

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem contourCauchySecondVariation_difference_bound
    (initial final first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    {parameterRadius : ℝ≥0} (positive : 0 < parameterRadius)
    (initial_nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
      ‖initial + parameter • second - standardCircleBanach‖ ≤ innerRadius)
    (final_nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
      ‖final + parameter • second - standardCircleBanach‖ ≤ innerRadius) :
    ‖contourCauchySecondVariation initial first second density -
      contourCauchySecondVariation final first second density‖ ≤
      (contourCauchyParameterOperatorConstant outerRadius * ‖initial - final‖ * ‖density‖) /
        ((outerRadius - innerRadius) / (‖first‖ + 1)) / (parameterRadius : ℝ) := by
  let auxiliaryRadius : ℝ≥0 := ⟨(outerRadius - innerRadius) / (‖first‖ + 1),
    div_nonneg (sub_nonneg.mpr gap.le) (by positivity)⟩
  have auxiliary_positive : 0 < auxiliaryRadius := div_pos (sub_pos.mpr gap) (by positivity)
  have holomorphic (data : PeriodicC1HolderHalf)
      (nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
        ‖data + parameter • second - standardCircleBanach‖ ≤ innerRadius) :
      DiffContOnCl ℂ (fun current : ℂ =>
        contourCauchyDirectionalDerivative (data + current • second) first density)
        (ball 0 parameterRadius) := by
    apply DiffContOnCl.mk_ball _
      (contourCauchyDirectionalDerivative_continuousOn_complex_line data first second density
        nonnegative gap small nearby)
    intro parameter member
    exact (contourCauchyDirectionalDerivative_hasDerivAt_complex_line data first second density parameter
      (((nearby parameter (ball_subset_closedBall member)).trans_lt gap).trans small)).differentiableAt.differentiableWithinAt
  have perturbations (data : PeriodicC1HolderHalf)
      (nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
        ‖data + parameter • second - standardCircleBanach‖ ≤ innerRadius)
      (parameter : ℂ) (member : parameter ∈ closedBall (0 : ℂ) parameterRadius)
      (auxiliary : ℂ) (auxiliary_member : auxiliary ∈ closedBall (0 : ℂ) auxiliaryRadius) :
      ‖data + parameter • second + auxiliary • first - standardCircleBanach‖ ≤ outerRadius := by
    have auxiliary_bound : ‖auxiliary‖ ≤ (outerRadius - innerRadius) / (‖first‖ + 1) := by
      simpa only [mem_closedBall, dist_zero_right] using auxiliary_member
    have product_bound := (le_div_iff₀ (by positivity : (0 : ℝ) < ‖first‖ + 1)).mp auxiliary_bound
    exact (complexContourPerturbation_distance (data + parameter • second) first auxiliary).trans
      (by have base_bound := nearby parameter member; nlinarith [norm_nonneg auxiliary])
  change ‖deriv (fun parameter : ℂ => contourCauchyDirectionalDerivative
      (initial + parameter • second) first density) 0 -
    deriv (fun parameter : ℂ => contourCauchyDirectionalDerivative
      (final + parameter • second) first density) 0‖ ≤ _
  apply cauchy_derivative_difference_bound positive
    (holomorphic initial initial_nearby) (holomorphic final final_nearby)
  intro parameter member
  have estimate := contourCauchyDirectionalDerivative_difference_bound
    (initial + parameter • second) (final + parameter • second) first density
    (nonnegative.trans gap.le) small auxiliary_positive
    (perturbations initial initial_nearby parameter (sphere_subset_closedBall member))
    (perturbations final final_nearby parameter (sphere_subset_closedBall member))
  have difference : initial + parameter • second - (final + parameter • second) = initial - final := by abel
  simpa only [difference] using estimate

theorem contourCauchySecondVariation_local_difference_bound
    (initial final first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (initial_near : ‖initial - standardCircleBanach‖ ≤ innerRadius)
    (final_near : ‖final - standardCircleBanach‖ ≤ innerRadius) :
    ‖contourCauchySecondVariation initial first second density -
      contourCauchySecondVariation final first second density‖ ≤
      (4 * contourCauchyParameterOperatorConstant outerRadius * (‖first‖ + 1) * (‖second‖ + 1) /
        (outerRadius - innerRadius) ^ 2) * ‖initial - final‖ * ‖density‖ := by
  let middle := (innerRadius + outerRadius) / 2
  let parameterRadius : ℝ≥0 := ⟨(outerRadius - innerRadius) / (2 * (‖second‖ + 1)),
    div_nonneg (sub_nonneg.mpr gap.le) (by positivity)⟩
  have positive : 0 < parameterRadius := div_pos (sub_pos.mpr gap) (by positivity)
  have nearby (data : PeriodicC1HolderHalf) (near : ‖data - standardCircleBanach‖ ≤ innerRadius)
      (parameter : ℂ) (member : parameter ∈ closedBall (0 : ℂ) parameterRadius) :
      ‖data + parameter • second - standardCircleBanach‖ ≤ middle := by
    have parameter_bound : ‖parameter‖ ≤ (outerRadius - innerRadius) / (2 * (‖second‖ + 1)) := by
      simpa only [mem_closedBall, dist_zero_right] using member
    have product_bound := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (‖second‖ + 1))).mp parameter_bound
    exact (complexContourPerturbation_distance data second parameter).trans
      (by dsimp only [middle]; nlinarith [norm_nonneg parameter])
  have estimate := contourCauchySecondVariation_difference_bound initial final first second density
    (innerRadius := middle) (outerRadius := outerRadius) (by dsimp only [middle]; linarith)
    (by dsimp only [middle]; linarith) small positive
    (nearby initial initial_near) (nearby final final_near)
  apply estimate.trans_eq
  change _ / ((outerRadius - middle) / (‖first‖ + 1)) /
      ((outerRadius - innerRadius) / (2 * (‖second‖ + 1))) = _
  dsimp only [middle]
  have gap_nonzero : outerRadius - innerRadius ≠ 0 := (sub_pos.mpr gap).ne'
  have first_nonzero : ‖first‖ + 1 ≠ 0 := ne_of_gt (by positivity)
  have second_nonzero : ‖second‖ + 1 ≠ 0 := ne_of_gt (by positivity)
  rw [show outerRadius - (innerRadius + outerRadius) / 2 = (outerRadius - innerRadius) / 2 by ring]
  field_simp [gap_nonzero, first_nonzero, second_nonzero]
  <;> ring

end

end EulerNonuniqueness.Paper
