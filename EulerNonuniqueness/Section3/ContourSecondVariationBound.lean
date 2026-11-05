import EulerNonuniqueness.Section3.ContourCauchySecondVariation

open Set Metric Filter
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem contourCauchySecondVariation_unit_norm_bound
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi))) (unit : ‖first‖ ≤ 1) :
    ‖contourCauchySecondVariation data first second density‖ ≤
      (2 * contourCauchyParameterOperatorConstant outerRadius * ‖density‖ /
        (outerRadius - innerRadius)) * ‖second‖ := by
  have inner_nonnegative : 0 ≤ innerRadius := (norm_nonneg _).trans near.le
  have operator_nonnegative : 0 ≤ contourCauchyParameterOperatorConstant outerRadius :=
    (contourCauchyParameterSupConstant_nonneg (inner_nonnegative.trans gap.le) small).trans
      (le_max_left _ _)
  unfold contourCauchySecondVariation
  apply norm_deriv_le_of_lip' (𝕜 := ℂ) (F := PeriodicHolderHalf)
    (f := fun parameter : ℂ =>
      contourCauchyDirectionalDerivative (data + parameter • second) first density) (x₀ := 0)
    (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) operator_nonnegative)
      (norm_nonneg _)) (sub_nonneg.mpr gap.le)) (norm_nonneg _))
  have positive : 0 < (innerRadius - ‖data - standardCircleBanach‖) / (‖second‖ + 1) :=
    div_pos (sub_pos.mpr near) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) positive] with parameter member
  have perturbed_near : ‖data + parameter • second - standardCircleBanach‖ < innerRadius := by
    apply complexContourPerturbation_near data second near
    simpa only [Metric.mem_ball, dist_zero_right] using member
  let auxiliaryRadius : ℝ≥0 := ⟨(outerRadius - innerRadius) / 2, by linarith⟩
  have auxiliary_positive : 0 < auxiliaryRadius := by
    change 0 < (outerRadius - innerRadius) / 2
    linarith
  have nearby (current : PeriodicC1HolderHalf)
      (current_near : ‖current - standardCircleBanach‖ ≤ innerRadius)
      (auxiliary : ℂ) (auxiliary_member : auxiliary ∈ closedBall (0 : ℂ) auxiliaryRadius) :
      ‖current + auxiliary • first - standardCircleBanach‖ ≤ outerRadius := by
    have auxiliary_bound : ‖auxiliary‖ ≤ (outerRadius - innerRadius) / 2 := by
      simpa only [mem_closedBall, dist_zero_right] using auxiliary_member
    have product_bound := mul_le_mul_of_nonneg_left unit (norm_nonneg auxiliary)
    exact (complexContourPerturbation_distance current first auxiliary).trans (by nlinarith)
  simp only [zero_smul, add_zero, sub_zero]
  have estimate := contourCauchyDirectionalDerivative_difference_bound
    (data + parameter • second) data first density (inner_nonnegative.trans gap.le)
    small auxiliary_positive (nearby _ perturbed_near.le) (nearby _ near.le)
  have subtraction : data + parameter • second - data = parameter • second := by abel
  rw [subtraction, norm_smul parameter second] at estimate
  exact estimate.trans_eq (by
    change contourCauchyParameterOperatorConstant outerRadius * (‖parameter‖ * ‖second‖) *
      ‖density‖ / ((outerRadius - innerRadius) / 2) = _
    field_simp
    ring)

theorem contourCauchySecondVariation_norm_bound
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    ‖contourCauchySecondVariation data first second density‖ ≤
      (2 * contourCauchyParameterOperatorConstant outerRadius * ‖density‖ /
        (outerRadius - innerRadius)) * ‖first‖ * ‖second‖ := by
  have data_small := near.trans (gap.trans small)
  by_cases zero : first = 0
  · subst first
    have zero_variation : contourCauchySecondVariation data 0 second density = 0 := by
      have actual := contourCauchySecondVariation_smul_left data 0 second density data_small (0 : ℂ)
      simpa only [zero_smul] using actual
    have zero_norm : ‖(0 : PeriodicC1HolderHalf)‖ = 0 := by
      simpa only [zero_smul, norm_zero, zero_mul] using norm_smul (0 : ℂ) data
    rw [zero_variation, norm_zero, zero_norm, mul_zero, zero_mul]
  have positive : 0 < ‖first‖ := (norm_pos_iff (a := first)).mpr zero
  have scalar_nonzero : (‖first‖ : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  let normalized : PeriodicC1HolderHalf := (‖first‖ : ℂ)⁻¹ • first
  have unit : ‖normalized‖ = 1 := by
    dsimp only [normalized]
    rw [norm_smul (‖first‖ : ℂ)⁻¹ first, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos positive, inv_mul_cancel₀ positive.ne']
  have restoration : (‖first‖ : ℂ) • normalized = first := by
    dsimp only [normalized]
    rw [smul_smul, mul_inv_cancel₀ scalar_nonzero, one_smul]
  have bound := contourCauchySecondVariation_unit_norm_bound data normalized second density
    near gap small unit.le
  have restored := contourCauchySecondVariation_smul_left data normalized second density
    data_small (‖first‖ : ℂ)
  rw [restoration] at restored
  rw [restored, norm_smul (‖first‖ : ℂ)
    (contourCauchySecondVariation data normalized second density),
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  exact (mul_le_mul_of_nonneg_left bound positive.le).trans_eq (by ring)

end

end EulerNonuniqueness.Paper
