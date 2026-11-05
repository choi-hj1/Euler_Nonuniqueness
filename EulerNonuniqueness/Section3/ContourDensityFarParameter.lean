import EulerNonuniqueness.Section3.ContourDensityParameter

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

noncomputable def contourCauchyParameterFarIntegrand (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) (jump source : ℝ) : ℂ :=
  ((contourCauchyKernel first.val.1 first.val.2.val.1 0 source -
      contourCauchyKernel first.val.1 first.val.2.val.1 jump source) -
    (contourCauchyKernel second.val.1 second.val.2.val.1 0 source -
      contourCauchyKernel second.val.1 second.val.2.val.1 jump source)) * (density.val.1 source - density.val.1 0)

theorem contourCauchyParameterFarIntegrand_bound (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius jump source : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8)
    (source_far : 2 * jump ≤ |source|) (source_bounded : |source| ≤ Real.pi) :
    ‖contourCauchyParameterFarIntegrand first second density jump source‖ ≤
      (‖first - second‖ * contourKernelParameterSmoothConstant radius * ‖density‖) * jump *
        |source| ^ (-(3 / 2 : ℝ)) := by
  have source_pos : 0 < |source| := by linarith
  have smooth_nonneg := contourKernelParameterSmoothConstant_nonneg radius_nonneg
  have identity : contourCauchyParameterFarIntegrand first second density jump source =
      ((contourCauchyKernel first.val.1 first.val.2.val.1 0 source -
          contourCauchyKernel second.val.1 second.val.2.val.1 0 source) -
        (contourCauchyKernel first.val.1 first.val.2.val.1 jump source -
          contourCauchyKernel second.val.1 second.val.2.val.1 jump source)) *
        (density.val.1 source - density.val.1 0) := by unfold contourCauchyParameterFarIntegrand; ring
  rw [identity, norm_mul]
  have density_bound : ‖density.val.1 source - density.val.1 0‖ ≤ ‖density‖ * Real.sqrt |source| := by
    simpa only [sub_zero] using PeriodicHolderHalf.holder_bound density source 0
  have smooth_bound := contourCauchyKernel_parameter_far_smoothness first second radius_nonneg radius_small
    first_near second_near jump_pos jump_small source_far source_bounded
  apply (mul_le_mul smooth_bound density_bound (norm_nonneg _) (by positivity)).trans_eq
  have power : Real.sqrt |source| / |source| ^ 2 = |source| ^ (-(3 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub source_pos]
    norm_num
  calc
    _ = (‖first - second‖ * contourKernelParameterSmoothConstant radius * ‖density‖) * jump *
        (Real.sqrt |source| / |source| ^ 2) := by unfold contourKernelParameterSmoothConstant; ring
    _ = _ := by rw [power]

theorem contourCauchy_weighted_far_intervalIntegrable (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {jump lower upper : ℝ} (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8)
    (ordered : lower ≤ upper) (lower_bound : -(5 * Real.pi / 4) ≤ lower)
    (upper_bound : upper ≤ 5 * Real.pi / 4) (same_side : upper < 0 ∨ jump < lower) :
    IntervalIntegrable (fun source => (contourCauchyKernel data.val.1 data.val.2.val.1 0 source -
      contourCauchyKernel data.val.1 data.val.2.val.1 jump source) * (density.val.1 source - density.val.1 0))
      volume lower upper := by
  have zero_near : |(0 : ℝ)| ≤ Real.pi / 4 := by rw [abs_zero]; positivity
  have jump_near : |jump| ≤ Real.pi / 4 := by rw [abs_of_pos jump_pos]; linarith [Real.pi_pos]
  have first_side : upper < 0 ∨ 0 < lower := same_side.imp id (fun bound => jump_pos.trans bound)
  have second_side : upper < jump ∨ jump < lower := same_side.imp (fun bound => bound.trans jump_pos) id
  exact ((banachContourCauchy_intervalIntegrable data small zero_near ordered lower_bound upper_bound first_side).sub
    (banachContourCauchy_intervalIntegrable data small jump_near ordered lower_bound upper_bound second_side)).mul_continuousOn
      (density.val.1.continuous.sub continuous_const).continuousOn

set_option maxHeartbeats 1000000 in
theorem contourCauchyParameterFarIntegrand_integral_right_bound (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius jump : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8) :
    ‖∫ source in (2 * jump)..Real.pi, contourCauchyParameterFarIntegrand first second density jump source‖ ≤
      (‖first - second‖ * contourKernelParameterSmoothConstant radius * ‖density‖) * Real.sqrt (2 * jump) := by
  have smooth_nonneg := contourKernelParameterSmoothConstant_nonneg radius_nonneg
  have estimate := norm_integral_far_half_bound (by positivity : 0 < 2 * jump)
    (by linarith [Real.pi_pos] : 2 * jump ≤ Real.pi)
    (show 0 ≤ (‖first - second‖ * contourKernelParameterSmoothConstant radius * ‖density‖) / 2 by positivity)
    (integrand := contourCauchyParameterFarIntegrand first second density jump)
    (fun source membership => by
      have source_pos : 0 < source := (by positivity : 0 < 2 * jump).trans membership.1
      have actual := contourCauchyParameterFarIntegrand_bound first second density radius_nonneg radius_small
        first_near second_near jump_pos jump_small
        (by rw [abs_of_pos source_pos]; exact membership.1.le)
        (by rw [abs_of_pos source_pos]; exact membership.2)
      rw [abs_of_pos source_pos] at actual
      convert actual using 1 <;> ring)
  convert estimate using 1 <;> ring

set_option maxHeartbeats 1000000 in
theorem contourCauchyParameterFarIntegrand_integral_left_bound (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius jump : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8) :
    ‖∫ source in (-Real.pi)..(-2 * jump), contourCauchyParameterFarIntegrand first second density jump source‖ ≤
      (‖first - second‖ * contourKernelParameterSmoothConstant radius * ‖density‖) * Real.sqrt (2 * jump) := by
  have smooth_nonneg := contourKernelParameterSmoothConstant_nonneg radius_nonneg
  have estimate := norm_integral_far_half_bound (by positivity : 0 < 2 * jump)
    (by linarith [Real.pi_pos] : 2 * jump ≤ Real.pi)
    (show 0 ≤ (‖first - second‖ * contourKernelParameterSmoothConstant radius * ‖density‖) / 2 by positivity)
    (integrand := fun source => contourCauchyParameterFarIntegrand first second density jump (-source))
    (fun source membership => by
      have source_pos : 0 < source := (by positivity : 0 < 2 * jump).trans membership.1
      have actual := contourCauchyParameterFarIntegrand_bound first second density radius_nonneg radius_small
        first_near second_near jump_pos jump_small
        (by rw [abs_neg, abs_of_pos source_pos]; exact membership.1.le)
        (by rw [abs_neg, abs_of_pos source_pos]; exact membership.2)
      rw [abs_neg, abs_of_pos source_pos] at actual
      convert actual using 1 <;> ring)
  rw [intervalIntegral.integral_comp_neg] at estimate
  convert estimate using 1 <;> congr 1 <;> ring

theorem contourCauchy_parameter_far_integral_difference (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (first_small : ‖first - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (second_small : ‖second - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {jump lower upper : ℝ} (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8)
    (ordered : lower ≤ upper) (lower_bound : -(5 * Real.pi / 4) ≤ lower)
    (upper_bound : upper ≤ 5 * Real.pi / 4) (same_side : upper < 0 ∨ jump < lower) :
    (∫ source in lower..upper,
      (contourCauchyKernel first.val.1 first.val.2.val.1 0 source -
        contourCauchyKernel first.val.1 first.val.2.val.1 jump source) * (density.val.1 source - density.val.1 0)) -
    (∫ source in lower..upper,
      (contourCauchyKernel second.val.1 second.val.2.val.1 0 source -
        contourCauchyKernel second.val.1 second.val.2.val.1 jump source) * (density.val.1 source - density.val.1 0)) =
      ∫ source in lower..upper, contourCauchyParameterFarIntegrand first second density jump source := by
  rw [← intervalIntegral.integral_sub
    (contourCauchy_weighted_far_intervalIntegrable first density first_small jump_pos jump_small ordered lower_bound upper_bound same_side)
    (contourCauchy_weighted_far_intervalIntegrable second density second_small jump_pos jump_small ordered lower_bound upper_bound same_side)]
  congr 1
  funext source
  unfold contourCauchyParameterFarIntegrand
  ring

theorem contourCauchyKernel_parameter_far_integral_difference_bound (first second : PeriodicC1HolderHalf)
    {radius target : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (target_pos : 0 < target) (target_small : target ≤ Real.pi / 8) :
    ‖((∫ source in (-Real.pi)..(-2 * target), contourCauchyKernel first.val.1 first.val.2.val.1 target source) +
        ∫ source in (2 * target)..Real.pi, contourCauchyKernel first.val.1 first.val.2.val.1 target source) -
      ((∫ source in (-Real.pi)..(-2 * target), contourCauchyKernel second.val.1 second.val.2.val.1 target source) +
        ∫ source in (2 * target)..Real.pi, contourCauchyKernel second.val.1 second.val.2.val.1 target source)‖ ≤
      ‖first - second‖ * contourKernelParameterSizeConstant radius * (4 * Real.sqrt Real.pi + 2) := by
  have target_near : |target| ≤ Real.pi / 4 := by rw [abs_of_pos target_pos]; linarith [Real.pi_pos]
  have left_integrable : ∀ data : PeriodicC1HolderHalf,
      ‖data - standardCircleBanach‖ ≤ radius →
      IntervalIntegrable (contourCauchyKernel data.val.1 data.val.2.val.1 target) volume (-Real.pi) (-2 * target) := by
    intro data nearby
    exact banachContourCauchy_intervalIntegrable data (nearby.trans_lt radius_small) target_near
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl (by linarith))
  have right_integrable : ∀ data : PeriodicC1HolderHalf,
      ‖data - standardCircleBanach‖ ≤ radius →
      IntervalIntegrable (contourCauchyKernel data.val.1 data.val.2.val.1 target) volume (2 * target) Real.pi := by
    intro data nearby
    exact banachContourCauchy_intervalIntegrable data (nearby.trans_lt radius_small) target_near
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inr (by linarith))
  have identity :
      ((∫ source in (-Real.pi)..(-2 * target), contourCauchyKernel first.val.1 first.val.2.val.1 target source) +
        ∫ source in (2 * target)..Real.pi, contourCauchyKernel first.val.1 first.val.2.val.1 target source) -
      ((∫ source in (-Real.pi)..(-2 * target), contourCauchyKernel second.val.1 second.val.2.val.1 target source) +
        ∫ source in (2 * target)..Real.pi, contourCauchyKernel second.val.1 second.val.2.val.1 target source) =
      (∫ source in (-Real.pi)..(-2 * target), contourCauchyKernel first.val.1 first.val.2.val.1 target source -
        contourCauchyKernel second.val.1 second.val.2.val.1 target source) +
      ∫ source in (2 * target)..Real.pi, contourCauchyKernel first.val.1 first.val.2.val.1 target source -
        contourCauchyKernel second.val.1 second.val.2.val.1 target source := by
    rw [intervalIntegral.integral_sub (left_integrable first first_near) (left_integrable second second_near),
      intervalIntegral.integral_sub (right_integrable first first_near) (right_integrable second second_near)]
    ring
  rw [identity]
  exact contourCauchyKernel_parameter_offCenter_far_bound first second radius_nonneg radius_small
    first_near second_near target_pos target_small

end EulerNonuniqueness.Paper
