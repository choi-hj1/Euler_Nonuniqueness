import EulerNonuniqueness.Section3.ContourKernelOffCenterParameter

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

noncomputable def contourKernelParameterSizeConstant (radius : ℝ) : ℝ :=
  1 / (2 / (3 * Real.pi) - radius) + (radius + 2) / (2 / (3 * Real.pi) - radius) ^ 2

noncomputable def contourKernelParameterSmoothConstant (radius : ℝ) : ℝ :=
  8 * (radius + 2) / (2 / (3 * Real.pi) - radius) ^ 2 +
    8 * (radius + 2) ^ 3 / (2 / (3 * Real.pi) - radius) ^ 4

theorem contourKernelParameterSizeConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourKernelParameterSizeConstant radius := by
  have chord_pos := sub_pos.mpr (radius_small.trans_le (min_le_right _ _))
  unfold contourKernelParameterSizeConstant
  positivity

theorem contourKernelParameterSmoothConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius) :
    0 ≤ contourKernelParameterSmoothConstant radius := by
  unfold contourKernelParameterSmoothConstant
  positivity

theorem density_kernel_inverseSqrt_bound {densityDifference kernel : ℂ} {holder constant distance : ℝ}
    (holder_nonneg : 0 ≤ holder) (constant_nonneg : 0 ≤ constant) (distance_pos : 0 < distance)
    (density_bound : ‖densityDifference‖ ≤ holder * Real.sqrt distance)
    (kernel_bound : ‖kernel‖ ≤ constant / distance) :
    ‖densityDifference * kernel‖ ≤ holder * constant / Real.sqrt distance := by
  rw [norm_mul]
  apply (mul_le_mul density_bound kernel_bound (norm_nonneg _) (by positivity)).trans_eq
  have root_pos := Real.sqrt_pos.mpr distance_pos
  field_simp
  calc
    _ = holder * constant * (Real.sqrt distance ^ 2) := by ring
    _ = _ := by rw [Real.sq_sqrt distance_pos.le]

theorem contourCauchyDensityRemainder_parameter_point_bound (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius target source : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (nearby : |source - target| ≤ 3 * Real.pi / 2) :
    ‖contourCauchyDensityRemainder first.val.1 first.val.2.val.1 density.val.1 target source -
      contourCauchyDensityRemainder second.val.1 second.val.2.val.1 density.val.1 target source‖ ≤
      (‖density‖ * (‖first - second‖ * contourKernelParameterSizeConstant radius)) * inverseSqrtDistance target source := by
  by_cases equal : source = target
  · subst source
    simp [contourCauchyDensityRemainder, inverseSqrtDistance]
  have identity : contourCauchyDensityRemainder first.val.1 first.val.2.val.1 density.val.1 target source -
      contourCauchyDensityRemainder second.val.1 second.val.2.val.1 density.val.1 target source =
      (density.val.1 source - density.val.1 target) *
        (contourCauchyKernel first.val.1 first.val.2.val.1 target source -
          contourCauchyKernel second.val.1 second.val.2.val.1 target source) := by
    unfold contourCauchyDensityRemainder contourCauchyKernel
    ring
  rw [identity]
  have chord_pos := sub_pos.mpr (radius_small.trans_le (min_le_right _ _))
  have kernel_bound := contourCauchyKernel_parameter_size first second (Ne.symm equal)
    (by linarith : 0 ≤ radius + 2) chord_pos (PeriodicC1HolderHalf.norm_le_radius_add_two second second_near)
    (by simpa only [abs_sub_comm target source] using PeriodicC1HolderHalf.chord_bound_of_radius first first_near nearby)
    (by simpa only [abs_sub_comm target source] using PeriodicC1HolderHalf.chord_bound_of_radius second second_near nearby)
  have actual := density_kernel_inverseSqrt_bound (norm_nonneg density)
    (mul_nonneg (norm_nonneg _) (contourKernelParameterSizeConstant_nonneg radius_nonneg radius_small))
    (abs_pos.mpr (sub_ne_zero.mpr equal)) (PeriodicHolderHalf.holder_bound density source target)
    (by simpa only [abs_sub_comm target source] using kernel_bound)
  exact actual

theorem contourCauchy_density_intervalIntegrable (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {target lower upper : ℝ} (target_near : |target| ≤ Real.pi / 4)
    (lower_mem : lower ∈ Icc (-Real.pi) Real.pi) (upper_mem : upper ∈ Icc (-Real.pi) Real.pi) :
    IntervalIntegrable (contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target)
      volume lower upper := by
  apply (banachContourCauchy_density_integrable_fixed_window data density small target_near).mono_set
  apply uIcc_subset_uIcc_iff_mem.mpr
  constructor
  · simpa only [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using lower_mem
  · simpa only [uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] using upper_mem

set_option maxHeartbeats 1000000 in
theorem contourCauchyDensityRemainder_parameter_near_bound (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius jump target : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8) (target_mem : target ∈ Icc 0 jump) :
    ‖(∫ source in (-2 * jump)..(2 * jump), contourCauchyDensityRemainder first.val.1 first.val.2.val.1 density.val.1 target source) -
      ∫ source in (-2 * jump)..(2 * jump), contourCauchyDensityRemainder second.val.1 second.val.2.val.1 density.val.1 target source‖ ≤
      8 * ‖density‖ * ‖first - second‖ * contourKernelParameterSizeConstant radius * Real.sqrt jump := by
  have target_near : |target| ≤ Real.pi / 4 := by rw [abs_of_nonneg target_mem.1]; linarith [target_mem.2, Real.pi_pos]
  have lower_mem : -2 * jump ∈ Icc (-Real.pi) Real.pi := by constructor <;> linarith [Real.pi_pos]
  have upper_mem : 2 * jump ∈ Icc (-Real.pi) Real.pi := by constructor <;> linarith [Real.pi_pos]
  rw [← intervalIntegral.integral_sub
    (contourCauchy_density_intervalIntegrable first density (first_near.trans_lt radius_small) target_near lower_mem upper_mem)
    (contourCauchy_density_intervalIntegrable second density (second_near.trans_lt radius_small) target_near lower_mem upper_mem)]
  have estimate := norm_setIntegral_weakSingular_near (radius := 4 * jump) (center := target)
    (domain := Ioc (-2 * jump) (2 * jump)) (by positivity)
    (show 0 ≤ ‖density‖ * (‖first - second‖ * contourKernelParameterSizeConstant radius) from by
      exact mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
        (contourKernelParameterSizeConstant_nonneg radius_nonneg radius_small))) measurableSet_Ioc
    (fun source membership => by constructor <;> linarith [membership.1, membership.2, target_mem.1, target_mem.2])
    (fun source membership => contourCauchyDensityRemainder_parameter_point_bound first second density
      radius_nonneg radius_small first_near second_near (by
        rw [abs_le]
        constructor <;> linarith [membership.1, membership.2, target_mem.1, target_mem.2, Real.pi_pos]))
  rw [← intervalIntegral.integral_of_le (by linarith : -2 * jump ≤ 2 * jump),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at estimate
  have sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [sqrt_four] at estimate
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Paper
