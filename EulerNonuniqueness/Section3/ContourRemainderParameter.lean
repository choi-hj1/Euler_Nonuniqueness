import EulerNonuniqueness.Section3.ContourKernelSmoothnessParameter

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

noncomputable def contourNormalizedTaylor (data : PeriodicC1HolderHalf) (target source : ℝ) : ℂ :=
  data.val.2.val.1 source + (data.val.1 target - data.val.1 source) / ((source - target : ℝ) : ℂ)

theorem contourNormalizedTaylor_bound (data : PeriodicC1HolderHalf) {target source : ℝ}
    (distinct : source ≠ target) :
    ‖contourNormalizedTaylor data target source‖ ≤ ‖data‖ * Real.sqrt |source - target| := by
  have distance_pos : 0 < |source - target| := abs_pos.mpr (sub_ne_zero.mpr distinct)
  have scalar_ne : ((source - target : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr distinct
  have actual := contour_taylor_remainder_unordered (source := target) (target := source)
    (norm_nonneg data) (fun current _ => PeriodicC1HolderHalf.hasDerivAt data current)
    (fun current _ => PeriodicC1HolderHalf.derivative_holder_bound data current source)
  have numerator_identity : data.val.1 target - data.val.1 source +
      ((source - target : ℝ) : ℂ) * data.val.2.val.1 source =
      -(data.val.1 source - data.val.1 target - (source - target) • data.val.2.val.1 source) := by
    rw [Complex.real_smul]
    ring
  have identity : contourNormalizedTaylor data target source =
      (data.val.1 target - data.val.1 source + ((source - target : ℝ) : ℂ) * data.val.2.val.1 source) /
        ((source - target : ℝ) : ℂ) := by
    unfold contourNormalizedTaylor
    have cast_ne : (source : ℂ) - (target : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr distinct
    field_simp [cast_ne]
    ring
  rw [identity, norm_div, numerator_identity, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  apply (div_le_div_of_nonneg_right actual (abs_nonneg _)).trans_eq
  field_simp

theorem contourNormalizedTaylor_sub (first second : PeriodicC1HolderHalf) (target source : ℝ) :
    contourNormalizedTaylor first target source - contourNormalizedTaylor second target source =
      contourNormalizedTaylor (first - second) target source := by
  unfold contourNormalizedTaylor
  change first.val.2.val.1 source + (first.val.1 target - first.val.1 source) / _ -
    (second.val.2.val.1 source + (second.val.1 target - second.val.1 source) / _) =
    first.val.2.val.1 source - second.val.2.val.1 source +
      ((first.val.1 target - second.val.1 target) - (first.val.1 source - second.val.1 source)) / _
  ring

theorem contourCauchyRemainder_eq_normalizedTaylor (data : PeriodicC1HolderHalf) {target source : ℝ}
    (distinct : source ≠ target) (separated : data.val.1 target - data.val.1 source ≠ 0) :
    contourCauchyRemainder data.val.1 data.val.2.val.1 target source =
      contourNormalizedTaylor data target source / (data.val.1 target - data.val.1 source) := by
  have scalar_ne : ((source - target : ℝ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr distinct
  unfold contourCauchyRemainder contourNormalizedTaylor
  field_simp

set_option maxHeartbeats 1000000 in
theorem contourCauchyRemainder_parameter_bound (first second : PeriodicC1HolderHalf)
    {target source speed chord : ℝ} (distinct : source ≠ target)
    (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord) (second_bound : ‖second‖ ≤ speed)
    (first_lower : chord * |source - target| ≤ ‖first.val.1 target - first.val.1 source‖)
    (second_lower : chord * |source - target| ≤ ‖second.val.1 target - second.val.1 source‖) :
    ‖contourCauchyRemainder first.val.1 first.val.2.val.1 target source -
      contourCauchyRemainder second.val.1 second.val.2.val.1 target source‖ ≤
      (‖first - second‖ * (1 / chord + speed / chord ^ 2)) / Real.sqrt |source - target| := by
  have distance_pos : 0 < |source - target| := abs_pos.mpr (sub_ne_zero.mpr distinct)
  have root_pos := Real.sqrt_pos.mpr distance_pos
  have first_pos := (mul_pos chord_pos distance_pos).trans_le first_lower
  have second_pos := (mul_pos chord_pos distance_pos).trans_le second_lower
  have first_ne := norm_ne_zero_iff.mp first_pos.ne'
  have second_ne := norm_ne_zero_iff.mp second_pos.ne'
  rw [contourCauchyRemainder_eq_normalizedTaylor first distinct first_ne,
    contourCauchyRemainder_eq_normalizedTaylor second distinct second_ne]
  have identity : contourNormalizedTaylor first target source / (first.val.1 target - first.val.1 source) -
      contourNormalizedTaylor second target source / (second.val.1 target - second.val.1 source) =
      (contourNormalizedTaylor first target source - contourNormalizedTaylor second target source) /
        (first.val.1 target - first.val.1 source) +
      contourNormalizedTaylor second target source *
        ((second.val.1 target - second.val.1 source) - (first.val.1 target - first.val.1 source)) /
        ((first.val.1 target - first.val.1 source) * (second.val.1 target - second.val.1 source)) := by
    field_simp
    ring
  rw [identity]
  apply (norm_add_le _ _).trans
  rw [norm_div, norm_div, norm_mul, norm_mul, contourNormalizedTaylor_sub,
    norm_sub_rev (second.val.1 target - second.val.1 source) (first.val.1 target - first.val.1 source)]
  have increment_bound : ‖(first.val.1 target - first.val.1 source) - (second.val.1 target - second.val.1 source)‖ ≤
      ‖first - second‖ * |source - target| := by
    simpa only [abs_sub_comm target source] using PeriodicC1HolderHalf.increment_difference_bound first second target source
  have second_numerator := (contourNormalizedTaylor_bound second distinct).trans
    (mul_le_mul_of_nonneg_right second_bound (Real.sqrt_nonneg _))
  calc
    _ ≤ (‖first - second‖ * Real.sqrt |source - target|) / (chord * |source - target|) +
        ((speed * Real.sqrt |source - target|) * (‖first - second‖ * |source - target|)) /
          ((chord * |source - target|) * (chord * |source - target|)) := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_right (contourNormalizedTaylor_bound (first - second) distinct) (norm_nonneg _)).trans
          (div_le_div_of_nonneg_left (by positivity) (mul_pos chord_pos distance_pos) first_lower)
      · exact (div_le_div_of_nonneg_right
          (mul_le_mul second_numerator increment_bound (norm_nonneg _) (by positivity)) (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul first_lower second_lower (by positivity) (norm_nonneg _)))
    _ = _ := by
      field_simp
      ring_nf
      rw [Real.sq_sqrt distance_pos.le]
      ring

end EulerNonuniqueness.Paper
