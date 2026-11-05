import EulerNonuniqueness.Section3.ContourBanachOperator
import EulerNonuniqueness.Section3.ContourPhaseParameter

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem complex_quotient_parameter_bound {first second firstDenominator secondDenominator : ℂ}
    {difference distance speed chord : ℝ} (difference_nonneg : 0 ≤ difference)
    (distance_pos : 0 < distance) (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (numerator_difference : ‖first - second‖ ≤ difference) (second_bound : ‖second‖ ≤ speed)
    (denominator_difference : ‖firstDenominator - secondDenominator‖ ≤ difference * distance)
    (first_lower : chord * distance ≤ ‖firstDenominator‖)
    (second_lower : chord * distance ≤ ‖secondDenominator‖) :
    ‖first / firstDenominator - second / secondDenominator‖ ≤
      difference * (1 / chord + speed / chord ^ 2) / distance := by
  have first_pos := (mul_pos chord_pos distance_pos).trans_le first_lower
  have second_pos := (mul_pos chord_pos distance_pos).trans_le second_lower
  have first_ne := norm_ne_zero_iff.mp first_pos.ne'
  have second_ne := norm_ne_zero_iff.mp second_pos.ne'
  have identity : first / firstDenominator - second / secondDenominator =
      (first - second) / firstDenominator + second * (secondDenominator - firstDenominator) /
        (firstDenominator * secondDenominator) := by
    field_simp
    ring
  rw [identity]
  apply (norm_add_le _ _).trans
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_sub_rev secondDenominator firstDenominator]
  calc
    _ ≤ difference / (chord * distance) +
        (speed * (difference * distance)) / ((chord * distance) * (chord * distance)) := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_right numerator_difference (norm_nonneg _)).trans
          (div_le_div_of_nonneg_left difference_nonneg (mul_pos chord_pos distance_pos) first_lower)
      · exact (div_le_div_of_nonneg_right
          (mul_le_mul second_bound denominator_difference (norm_nonneg _) speed_nonneg) (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul first_lower second_lower (by positivity) (norm_nonneg _)))
    _ = _ := by field_simp; ring

theorem complex_squared_quotient_parameter_bound {first second firstDenominator secondDenominator : ℂ}
    {difference distance speed chord : ℝ} (difference_nonneg : 0 ≤ difference)
    (distance_pos : 0 < distance) (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (numerator_difference : ‖first - second‖ ≤ 2 * speed * difference)
    (second_bound : ‖second‖ ≤ speed ^ 2)
    (denominator_difference : ‖firstDenominator - secondDenominator‖ ≤ difference * distance)
    (denominator_sum : ‖firstDenominator + secondDenominator‖ ≤ 2 * speed * distance)
    (first_lower : chord * distance ≤ ‖firstDenominator‖)
    (second_lower : chord * distance ≤ ‖secondDenominator‖) :
    ‖first / firstDenominator ^ 2 - second / secondDenominator ^ 2‖ ≤
      difference * (2 * speed / chord ^ 2 + 2 * speed ^ 3 / chord ^ 4) / distance ^ 2 := by
  have first_pos := (mul_pos chord_pos distance_pos).trans_le first_lower
  have second_pos := (mul_pos chord_pos distance_pos).trans_le second_lower
  have first_ne := norm_ne_zero_iff.mp first_pos.ne'
  have second_ne := norm_ne_zero_iff.mp second_pos.ne'
  have first_square : (chord * distance) ^ 2 ≤ ‖firstDenominator‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) first_lower 2
  have second_square : (chord * distance) ^ 2 ≤ ‖secondDenominator‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) second_lower 2
  have identity : first / firstDenominator ^ 2 - second / secondDenominator ^ 2 =
      (first - second) / firstDenominator ^ 2 +
        second * (secondDenominator - firstDenominator) * (secondDenominator + firstDenominator) /
          (firstDenominator ^ 2 * secondDenominator ^ 2) := by
    field_simp
    ring
  rw [identity]
  apply (norm_add_le _ _).trans
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_sub_rev secondDenominator firstDenominator, add_comm secondDenominator firstDenominator]
  calc
    _ ≤ (2 * speed * difference) / (chord * distance) ^ 2 +
        (speed ^ 2 * (difference * distance) * (2 * speed * distance)) /
          ((chord * distance) ^ 2 * (chord * distance) ^ 2) := by
      apply add_le_add
      · exact (div_le_div_of_nonneg_right numerator_difference (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) first_square)
      · exact (div_le_div_of_nonneg_right
          (mul_le_mul
            (mul_le_mul second_bound denominator_difference (norm_nonneg _) (by positivity))
            denominator_sum (norm_nonneg _) (by positivity)) (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul first_square second_square (by positivity) (by positivity)))
    _ = _ := by field_simp; ring

theorem PeriodicC1HolderHalf.norm_le_radius_add_two (data : PeriodicC1HolderHalf) {radius : ℝ}
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) : ‖data‖ ≤ radius + 2 := by
  have triangle := norm_add_le (data - standardCircleBanach) standardCircleBanach
  rw [sub_add_cancel data standardCircleBanach] at triangle
  linarith [standardCircleBanach_norm_bound]

theorem PeriodicC1HolderHalf.chord_bound_of_radius (data : PeriodicC1HolderHalf) {radius target source : ℝ}
    (near_circle : ‖data - standardCircleBanach‖ ≤ radius) (nearby : |source - target| ≤ 3 * Real.pi / 2) :
    (2 / (3 * Real.pi) - radius) * |source - target| ≤ ‖data.val.1 target - data.val.1 source‖ := by
  exact (mul_le_mul_of_nonneg_right (by linarith :
    2 / (3 * Real.pi) - radius ≤ 2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) (abs_nonneg _)).trans
      (PeriodicC1HolderHalf.chord_bound_extended data nearby)

theorem contourCauchyKernel_parameter_size (first second : PeriodicC1HolderHalf)
    {target source speed chord : ℝ} (distinct : target ≠ source)
    (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (second_bound : ‖second‖ ≤ speed)
    (first_lower : chord * |target - source| ≤ ‖first.val.1 target - first.val.1 source‖)
    (second_lower : chord * |target - source| ≤ ‖second.val.1 target - second.val.1 source‖) :
    ‖contourCauchyKernel first.val.1 first.val.2.val.1 target source -
      contourCauchyKernel second.val.1 second.val.2.val.1 target source‖ ≤
      ‖first - second‖ * (1 / chord + speed / chord ^ 2) / |target - source| := by
  exact complex_quotient_parameter_bound (norm_nonneg _) (abs_pos.mpr (sub_ne_zero.mpr distinct))
    speed_nonneg chord_pos (PeriodicC1HolderHalf.speed_bound (first - second) source)
    ((PeriodicC1HolderHalf.speed_bound second source).trans second_bound)
    (PeriodicC1HolderHalf.increment_difference_bound first second target source) first_lower second_lower

noncomputable def contourCauchyKernelTargetDerivative (data : PeriodicC1HolderHalf) (target source : ℝ) : ℂ :=
  -(data.val.2.val.1 source * data.val.2.val.1 target) / (data.val.1 target - data.val.1 source) ^ 2

theorem contourCauchyKernel_hasDerivAt_target (data : PeriodicC1HolderHalf) {target source : ℝ}
    (separated : data.val.1 target - data.val.1 source ≠ 0) :
    HasDerivAt (fun parameter => contourCauchyKernel data.val.1 data.val.2.val.1 parameter source)
      (contourCauchyKernelTargetDerivative data target source) target := by
  have actual := (hasDerivAt_const target (data.val.2.val.1 source)).div
    ((PeriodicC1HolderHalf.hasDerivAt data target).sub_const (data.val.1 source)) separated
  simpa only [zero_mul, zero_sub, contourCauchyKernelTargetDerivative] using actual

theorem contourCauchyKernelTargetDerivative_parameter_bound (first second : PeriodicC1HolderHalf)
    {target source speed chord : ℝ} (distinct : target ≠ source)
    (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (first_bound : ‖first‖ ≤ speed) (second_bound : ‖second‖ ≤ speed)
    (first_lower : chord * |target - source| ≤ ‖first.val.1 target - first.val.1 source‖)
    (second_lower : chord * |target - source| ≤ ‖second.val.1 target - second.val.1 source‖) :
    ‖contourCauchyKernelTargetDerivative first target source - contourCauchyKernelTargetDerivative second target source‖ ≤
      ‖first - second‖ * (2 * speed / chord ^ 2 + 2 * speed ^ 3 / chord ^ 4) / |target - source| ^ 2 := by
  have first_speed : ∀ label : ℝ, ‖first.val.2.val.1 label‖ ≤ speed :=
    fun label => (PeriodicC1HolderHalf.speed_bound first label).trans first_bound
  have second_speed : ∀ label : ℝ, ‖second.val.2.val.1 label‖ ≤ speed :=
    fun label => (PeriodicC1HolderHalf.speed_bound second label).trans second_bound
  have product_bound : ‖first.val.2.val.1 source * first.val.2.val.1 target -
      second.val.2.val.1 source * second.val.2.val.1 target‖ ≤ 2 * speed * ‖first - second‖ := by
    have identity : first.val.2.val.1 source * first.val.2.val.1 target -
        second.val.2.val.1 source * second.val.2.val.1 target =
        (first.val.2.val.1 source - second.val.2.val.1 source) * first.val.2.val.1 target +
          second.val.2.val.1 source * (first.val.2.val.1 target - second.val.2.val.1 target) := by ring
    rw [identity]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    have source_difference := PeriodicC1HolderHalf.speed_bound (first - second) source
    have target_difference := PeriodicC1HolderHalf.speed_bound (first - second) target
    change ‖first.val.2.val.1 source - second.val.2.val.1 source‖ ≤ ‖first - second‖ at source_difference
    change ‖first.val.2.val.1 target - second.val.2.val.1 target‖ ≤ ‖first - second‖ at target_difference
    apply (add_le_add
      (mul_le_mul source_difference (first_speed target) (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul (second_speed source) target_difference (norm_nonneg _) speed_nonneg)).trans_eq
    ring
  have sum_bound : ‖(first.val.1 target - first.val.1 source) + (second.val.1 target - second.val.1 source)‖ ≤
      2 * speed * |target - source| := by
    apply (norm_add_le _ _).trans
    have first_increment := (PeriodicC1HolderHalf.lipschitz_bound first target source).trans
      (mul_le_mul_of_nonneg_right first_bound (abs_nonneg _))
    have second_increment := (PeriodicC1HolderHalf.lipschitz_bound second target source).trans
      (mul_le_mul_of_nonneg_right second_bound (abs_nonneg _))
    linarith
  have actual := complex_squared_quotient_parameter_bound (norm_nonneg _)
    (abs_pos.mpr (sub_ne_zero.mpr distinct)) speed_nonneg chord_pos product_bound
    (by rw [norm_mul]; exact (mul_le_mul (second_speed source) (second_speed target) (norm_nonneg _) speed_nonneg).trans_eq (by ring))
    (PeriodicC1HolderHalf.increment_difference_bound first second target source) sum_bound first_lower second_lower
  unfold contourCauchyKernelTargetDerivative
  simpa only [neg_div, neg_sub_neg, norm_sub_rev] using actual

end EulerNonuniqueness.Paper
