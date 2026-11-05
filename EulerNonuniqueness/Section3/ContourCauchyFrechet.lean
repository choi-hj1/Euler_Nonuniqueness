import EulerNonuniqueness.Section3.ContourCauchyDirectionalDerivative
import EulerNonuniqueness.Section3.CauchyTaylorRemainder
import EulerNonuniqueness.Section3.ContourCauchyOperatorLipschitz

open Set Metric Filter MeasureTheory
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem extendedContourCauchy_differentiableAt_complex_line (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) (parameter : ℂ)
    (small : ‖data + parameter • direction - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℂ (fun current : ℂ => extendedContourCauchy (data + current • direction) density) parameter := by
  have actual := (analyticAt_extendedContourCauchy_complex_line
    (data + parameter • direction) direction density small).differentiableAt
  have outer : DifferentiableAt ℂ (fun current : ℂ =>
      extendedContourCauchy (data + parameter • direction + current • direction) density)
      (parameter - parameter) := by simpa only [sub_self] using actual
  have inner : DifferentiableAt ℂ (fun current : ℂ => current - parameter) parameter :=
    differentiableAt_id.sub (differentiableAt_const parameter)
  have translated := outer.comp (f := fun current : ℂ => current - parameter) parameter inner
  apply translated.congr_of_eventuallyEq
  filter_upwards [] with current
  dsimp only [Function.comp_apply]
  have identity : data + parameter • direction + (current - parameter) • direction = data + current • direction := by
    rw [sub_smul current parameter direction]
    abel
  rw [identity]

theorem extendedContourCauchy_uniform_norm_bound (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (nonnegative : 0 ≤ radius) (small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖extendedContourCauchy data density‖ ≤ contourCauchyUniformOperatorConstant radius * ‖density‖ := by
  rw [extendedContourCauchy_eq _ _ (nearby.trans_lt small)]
  exact (contourCauchyOperatorCLM data (nearby.trans_lt small)).le_opNorm density |>.trans
    (mul_le_mul_of_nonneg_right (contourCauchyOperatorCLM_uniform_norm_bound data nonnegative small nearby) (norm_nonneg _))

theorem contourCauchy_complex_line_remainder_bound (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius : ℝ} (nonnegative : 0 ≤ radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) {parameterRadius : ℝ≥0} (positive : 0 < parameterRadius)
    (nearby : ∀ parameter ∈ closedBall (0 : ℂ) parameterRadius,
      ‖data + parameter • direction - standardCircleBanach‖ ≤ radius)
    {parameter : ℂ} (parameter_small : 2 * ‖parameter‖ ≤ parameterRadius) :
    ‖extendedContourCauchy (data + parameter • direction) density - extendedContourCauchy data density -
      parameter • contourCauchyDirectionalDerivative data direction density‖ ≤
      (2 * (contourCauchyUniformOperatorConstant radius * ‖density‖) / (parameterRadius : ℝ) ^ 2) * ‖parameter‖ ^ 2 := by
  have continuous := extendedContourCauchy_continuousOn_complex_line data direction density nonnegative small nearby
  have holomorphic : DiffContOnCl ℂ (fun current : ℂ => extendedContourCauchy (data + current • direction) density)
      (ball 0 parameterRadius) := by
    apply DiffContOnCl.mk_ball _ continuous
    intro current member
    exact (extendedContourCauchy_differentiableAt_complex_line data direction density current
      ((nearby current (ball_subset_closedBall member)).trans_lt small)).differentiableWithinAt
  have estimate := cauchy_first_remainder_bound positive holomorphic parameter_small
    (fun current member => extendedContourCauchy_uniform_norm_bound _ density nonnegative small
      (nearby current (sphere_subset_closedBall member)))
  simpa only [zero_smul, add_zero, contourCauchyDirectionalDerivative] using estimate

theorem contourCauchy_quadratic_remainder_bound (data increment : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4) :
    ‖extendedContourCauchy (data + increment) density - extendedContourCauchy data density -
      contourCauchyDirectionalDerivative data increment density‖ ≤
      (8 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 := by
  by_cases zero : increment = 0
  · subst increment
    have derivative_zero : contourCauchyDirectionalDerivative data 0 density = 0 := by
      have linear := contourCauchyDirectionalDerivative_smul data (0 : PeriodicC1HolderHalf) density (near.trans small) (0 : ℂ)
      simpa only [zero_smul] using linear
    have zero_norm : ‖(0 : PeriodicC1HolderHalf)‖ = 0 := by
      simpa only [zero_smul, norm_zero, zero_mul] using norm_smul (0 : ℂ) data
    have holder_zero_norm : ‖(0 : PeriodicHolderHalf)‖ = 0 := by
      simpa only [zero_smul, norm_zero, zero_mul] using norm_smul (0 : ℂ) density
    simp only [add_zero, sub_self, derivative_zero, sub_zero, zero_norm, holder_zero_norm,
      zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, le_refl]
  have increment_positive : 0 < ‖increment‖ := (norm_pos_iff (a := increment)).mpr zero
  have scalar_ne : (‖increment‖ : ℂ) ≠ 0 := by exact_mod_cast increment_positive.ne'
  let direction : PeriodicC1HolderHalf := (‖increment‖ : ℂ)⁻¹ • increment
  have direction_norm : ‖direction‖ = 1 := by
    dsimp only [direction]
    rw [norm_smul (‖increment‖ : ℂ)⁻¹ increment, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos increment_positive, inv_mul_cancel₀ increment_positive.ne']
  have restoration : (‖increment‖ : ℂ) • direction = increment := by
    dsimp only [direction]
    rw [smul_smul, mul_inv_cancel₀ scalar_ne, one_smul]
  let parameterRadius : ℝ≥0 := ⟨(radius - ‖data - standardCircleBanach‖) / 2,
    div_nonneg (sub_nonneg.mpr near.le) (by norm_num)⟩
  have parameter_positive : 0 < parameterRadius := by
    change 0 < (radius - ‖data - standardCircleBanach‖) / 2
    linarith
  have nearby (parameter : ℂ) (member : parameter ∈ closedBall 0 (parameterRadius : ℝ)) :
      ‖data + parameter • direction - standardCircleBanach‖ ≤ radius := by
    have parameter_bound : ‖parameter‖ ≤ parameterRadius := by simpa only [mem_closedBall, dist_zero_right] using member
    have estimate := complexContourPerturbation_distance data direction parameter
    rw [direction_norm, mul_one] at estimate
    change ‖parameter‖ ≤ (radius - ‖data - standardCircleBanach‖) / 2 at parameter_bound
    exact estimate.trans (by linarith)
  have parameter_small : 2 * ‖(‖increment‖ : ℂ)‖ ≤ parameterRadius := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos increment_positive]
    change 2 * ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 2
    linarith
  have estimate := contourCauchy_complex_line_remainder_bound data direction density
    ((norm_nonneg _).trans near.le) small parameter_positive nearby parameter_small
  rw [restoration, ← contourCauchyDirectionalDerivative_smul data direction density (near.trans small),
    restoration, Complex.norm_real, Real.norm_eq_abs, abs_of_pos increment_positive] at estimate
  exact estimate.trans_eq (by dsimp only [parameterRadius]; field_simp; ring)

theorem hasFDerivAt_extendedContourCauchy (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt (fun current : PeriodicC1HolderHalf => extendedContourCauchy current density)
      (contourCauchyDerivativeCLM data density near small) data := by
  apply (hasFDerivAt_iff_isLittleO_nhds_zero (𝕜 := ℂ)
    (f := fun current : PeriodicC1HolderHalf => extendedContourCauchy current density)
    (f' := contourCauchyDerivativeCLM data density near small) (x := data)).mpr
  have remainder_bound : (fun increment : PeriodicC1HolderHalf =>
      extendedContourCauchy (data + increment) density - extendedContourCauchy data density -
        (contourCauchyDerivativeCLM data density near small) increment) =O[𝓝 0]
      (fun increment : PeriodicC1HolderHalf => ‖increment‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound
      (8 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 2)
    have positive : 0 < (radius - ‖data - standardCircleBanach‖) / 4 := by linarith
    filter_upwards [Metric.ball_mem_nhds (0 : PeriodicC1HolderHalf) positive] with increment member
    have increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4 := by
      have norm_small : ‖increment‖ < (radius - ‖data - standardCircleBanach‖) / 4 := by
        simpa only [mem_ball, dist_zero_right] using member
      exact norm_small.le
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖increment‖)] using
      contourCauchy_quadratic_remainder_bound data increment density near small increment_small
  exact remainder_bound.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := PeriodicC1HolderHalf) (by decide : 1 < (2 : ℕ)))

end

end EulerNonuniqueness.Paper
