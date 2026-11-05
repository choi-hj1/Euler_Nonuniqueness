import EulerNonuniqueness.Section3.ContourCauchyOffCenter
import EulerNonuniqueness.Section3.ContourPhaseParameter

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

set_option maxHeartbeats 1000000 in
theorem banachContourCauchy_density_near_bound (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {jump target : ℝ} (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8)
    (target_mem : target ∈ Icc 0 jump) :
    ‖∫ source in (-2 * jump)..(2 * jump),
      contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target source‖ ≤
      (8 * (‖density‖ * ‖data‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖))) * Real.sqrt jump := by
  have chord_pos := sub_pos.mpr (small.trans_le (min_le_right _ _))
  have estimate := contourCauchyDensityRemainder_near_bound (radius := 4 * jump)
    (domain := Ioc (-2 * jump) (2 * jump)) (by positivity)
    (norm_nonneg density) (norm_nonneg data) chord_pos measurableSet_Ioc
    (fun source membership => by
      constructor <;> linarith [membership.1, membership.2, target_mem.1, target_mem.2])
    (fun source _ => PeriodicHolderHalf.holder_bound density source target)
    (fun source _ => PeriodicC1HolderHalf.speed_bound data source)
    (fun source membership => by
      apply PeriodicC1HolderHalf.chord_bound_extended data
      rw [abs_le]
      constructor <;> linarith [membership.1, membership.2, target_mem.1, target_mem.2, Real.pi_pos])
  rw [← intervalIntegral.integral_of_le (by linarith : -2 * jump ≤ 2 * jump)] at estimate
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at estimate
  have sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [sqrt_four] at estimate
  convert estimate using 1 <;> ring

set_option maxHeartbeats 1000000 in
theorem banachContourCauchy_density_far_right_bound (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {jump : ℝ} (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8) :
    ‖∫ source in (2 * jump)..Real.pi,
      (contourCauchyKernel data.val.1 data.val.2.val.1 0 source -
        contourCauchyKernel data.val.1 data.val.2.val.1 jump source) * (density.val.1 source - density.val.1 0)‖ ≤
      (2 * ‖data‖ ^ 2 * ‖density‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) ^ 2) *
        Real.sqrt (2 * jump) := by
  have chord_pos := sub_pos.mpr (small.trans_le (min_le_right _ _))
  have actual := contourCauchy_density_far_integral_bound
    (curve := data.val.1) (tangent := data.val.2.val.1) (density := density.val.1)
    jump_pos.ne' (by rw [abs_of_pos jump_pos]; linarith [Real.pi_pos] : 2 * |jump| ≤ Real.pi)
    (norm_nonneg data) chord_pos (norm_nonneg density)
    (fun source _ => PeriodicC1HolderHalf.speed_bound data source)
    (by simpa only [zero_sub, abs_neg] using PeriodicC1HolderHalf.lipschitz_bound data 0 jump)
    (fun source membership => by
      have source_pos : 0 < source := (by positivity : 0 < 2 * |jump|).trans membership.1
      have nearby : |source - (0 : ℝ)| ≤ 3 * Real.pi / 2 := by
        rw [sub_zero, abs_of_pos source_pos]
        linarith [membership.2, Real.pi_pos]
      simpa only [sub_zero, abs_of_pos source_pos] using PeriodicC1HolderHalf.chord_bound_extended data nearby)
    (fun source membership => by
      have nearby : |source - jump| ≤ 3 * Real.pi / 2 := by
        rw [abs_le]
        constructor <;> linarith [membership.1, membership.2, abs_nonneg jump, Real.pi_pos]
      simpa only [abs_sub_comm jump source] using PeriodicC1HolderHalf.chord_bound_extended data nearby)
    (fun source membership => by
      have source_pos : 0 < source := (by positivity : 0 < 2 * |jump|).trans membership.1
      simpa only [sub_zero, abs_of_pos source_pos] using PeriodicHolderHalf.holder_bound density source 0)
  simpa only [abs_of_pos jump_pos] using actual

set_option maxHeartbeats 1000000 in
theorem banachContourCauchy_density_far_left_bound (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {jump : ℝ} (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8) :
    ‖∫ source in (-Real.pi)..(-2 * jump),
      (contourCauchyKernel data.val.1 data.val.2.val.1 0 source -
        contourCauchyKernel data.val.1 data.val.2.val.1 jump source) * (density.val.1 source - density.val.1 0)‖ ≤
      (2 * ‖data‖ ^ 2 * ‖density‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) ^ 2) *
        Real.sqrt (2 * jump) := by
  let curve := fun source => data.val.1 (-source)
  let tangent := fun source => data.val.2.val.1 (-source)
  let reflectedDensity := fun source => density.val.1 (-source)
  have chord_pos := sub_pos.mpr (small.trans_le (min_le_right _ _))
  have actual := contourCauchy_density_far_integral_bound
    (curve := curve) (tangent := tangent) (density := reflectedDensity) (second := -jump)
    (neg_ne_zero.mpr jump_pos.ne')
    (by rw [abs_neg, abs_of_pos jump_pos]; linarith [Real.pi_pos] : 2 * |-jump| ≤ Real.pi)
    (norm_nonneg data) chord_pos (norm_nonneg density)
    (fun source _ => PeriodicC1HolderHalf.speed_bound data (-source))
    (by simpa only [curve, neg_zero, neg_neg, zero_sub, abs_neg] using
      PeriodicC1HolderHalf.lipschitz_bound data 0 jump)
    (fun source membership => by
      have source_pos : 0 < source := (by rw [abs_neg, abs_of_pos jump_pos]; positivity : 0 < 2 * |-jump|).trans membership.1
      have nearby : |-source - (0 : ℝ)| ≤ 3 * Real.pi / 2 := by
        rw [sub_zero, abs_neg, abs_of_pos source_pos]
        linarith [membership.2, Real.pi_pos]
      simpa only [curve, neg_zero, sub_zero, abs_neg, abs_of_pos source_pos] using
        PeriodicC1HolderHalf.chord_bound_extended data nearby)
    (fun source membership => by
      have source_pos : 0 < source := (by rw [abs_neg, abs_of_pos jump_pos]; positivity : 0 < 2 * |-jump|).trans membership.1
      have nearby : |-source - jump| ≤ 3 * Real.pi / 2 := by
        rw [abs_of_neg (by linarith)]
        linarith [membership.2, Real.pi_pos]
      have bound := PeriodicC1HolderHalf.chord_bound_extended data nearby
      have distance : |-source - jump| = |-jump - source| := by congr 1; ring
      simpa only [curve, neg_neg, distance] using bound)
    (fun source membership => by
      have source_pos : 0 < source := (by rw [abs_neg, abs_of_pos jump_pos]; positivity : 0 < 2 * |-jump|).trans membership.1
      simpa only [reflectedDensity, neg_zero, sub_zero, abs_neg, abs_of_pos source_pos] using
        PeriodicHolderHalf.holder_bound density (-source) 0)
  have integrand_identity : (fun source =>
      (contourCauchyKernel curve tangent 0 source - contourCauchyKernel curve tangent (-jump) source) *
        (reflectedDensity source - reflectedDensity 0)) =
      (fun source => (contourCauchyKernel data.val.1 data.val.2.val.1 0 (-source) -
        contourCauchyKernel data.val.1 data.val.2.val.1 jump (-source)) *
          (density.val.1 (-source) - density.val.1 0)) := by
    funext source
    simp only [contourCauchyKernel, curve, tangent, reflectedDensity, neg_zero, neg_neg]
  rw [integrand_identity, abs_neg, abs_of_pos jump_pos] at actual
  have reflection := intervalIntegral.integral_comp_neg
    (fun source => (contourCauchyKernel data.val.1 data.val.2.val.1 0 source -
      contourCauchyKernel data.val.1 data.val.2.val.1 jump source) * (density.val.1 source - density.val.1 0))
    (a := 2 * jump) (b := Real.pi)
  rw [reflection] at actual
  simpa only [neg_mul] using actual

theorem banachContourCauchy_density_integrable_fixed_window (data : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {target : ℝ} (target_near : |target| ≤ Real.pi / 4) :
    IntervalIntegrable (contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target)
      volume (-Real.pi) Real.pi := by
  have target_bounds := abs_le.mp target_near
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)).mpr
  apply contourCauchyDensityRemainder_integrable_interval (norm_nonneg density) (norm_nonneg data)
    (sub_pos.mpr (small.trans_le (min_le_right _ _)))
    data.val.1.continuous data.val.2.val.1.continuous density.val.1.continuous
    (fun source _ => PeriodicHolderHalf.holder_bound density source target)
    (fun source _ => PeriodicC1HolderHalf.speed_bound data source)
  intro source membership
  apply PeriodicC1HolderHalf.chord_bound_extended data
  rw [abs_le]
  constructor <;> linarith [membership.1, membership.2, target_bounds.1, target_bounds.2, Real.pi_pos]

theorem banachContourCauchyTransform_eq_fixed_window (data : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) (target : ℝ) :
    contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 target =
      (∫ source in (-Real.pi)..Real.pi,
        contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target source) -
        (Real.pi : ℂ) * Complex.I * density.val.1 target := by
  have periodic : Function.Periodic
      (contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target) (2 * Real.pi) := by
    intro source
    unfold contourCauchyDensityRemainder
    rw [PeriodicC1HolderHalf.periodic data source, PeriodicHolderHalf.periodic data.val.2 source,
      PeriodicHolderHalf.periodic density source]
  have windows := periodic.intervalIntegral_add_eq (target - Real.pi) (-Real.pi)
  unfold contourCauchyTransform
  congr 1
  convert windows using 1 <;> congr 1 <;> ring

theorem contourCauchyDensityRemainder_far_difference_identity {curve tangent density : ℝ → ℂ}
    {first second lower upper : ℝ}
    (density_continuous : Continuous density)
    (first_integrable : IntervalIntegrable (contourCauchyKernel curve tangent first) volume lower upper)
    (second_integrable : IntervalIntegrable (contourCauchyKernel curve tangent second) volume lower upper) :
    (∫ source in lower..upper, contourCauchyDensityRemainder curve tangent density first source) -
      (∫ source in lower..upper, contourCauchyDensityRemainder curve tangent density second source) =
      (∫ source in lower..upper,
        (contourCauchyKernel curve tangent first source - contourCauchyKernel curve tangent second source) *
          (density source - density first)) +
        (density second - density first) * ∫ source in lower..upper, contourCauchyKernel curve tangent second source := by
  have remainder_identity : ∀ target : ℝ, contourCauchyDensityRemainder curve tangent density target =
      (fun source => contourCauchyKernel curve tangent target source * (density source - density target)) := by
    intro target
    funext source
    simp only [contourCauchyKernel, contourCauchyDensityRemainder]
    ring
  simp_rw [remainder_identity]
  rw [← intervalIntegral.integral_sub
    (first_integrable.mul_continuousOn (density_continuous.sub continuous_const).continuousOn)
    (second_integrable.mul_continuousOn (density_continuous.sub continuous_const).continuousOn)]
  have identity : (fun source => contourCauchyKernel curve tangent first source * (density source - density first) -
      contourCauchyKernel curve tangent second source * (density source - density second)) =
      (fun source => (contourCauchyKernel curve tangent first source - contourCauchyKernel curve tangent second source) *
        (density source - density first) + (density second - density first) * contourCauchyKernel curve tangent second source) := by
    funext source
    ring
  rw [identity, intervalIntegral.integral_add
    ((first_integrable.sub second_integrable).mul_continuousOn (density_continuous.sub continuous_const).continuousOn)
    (second_integrable.const_mul _), intervalIntegral.integral_const_mul]

end EulerNonuniqueness.Paper
