import EulerNonuniqueness.Section3.ContourCauchyHolderEstimates

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem intervalIntegral_three_parts {function : ℝ → ℂ} {first second third fourth : ℝ}
    (first_integrable : IntervalIntegrable function volume first second)
    (second_integrable : IntervalIntegrable function volume second third)
    (third_integrable : IntervalIntegrable function volume third fourth) :
    (∫ source in first..fourth, function source) =
      (∫ source in first..second, function source) + (∫ source in second..third, function source) +
        ∫ source in third..fourth, function source := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (first_integrable.trans second_integrable) third_integrable,
    ← intervalIntegral.integral_add_adjacent_intervals first_integrable second_integrable]

set_option maxHeartbeats 1000000 in
theorem banachContourCauchyTransform_difference_decomposition (data : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {jump : ℝ} (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8) :
    contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 0 -
      contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 jump =
    ((∫ source in (-2 * jump)..(2 * jump),
        contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 0 source) -
      ∫ source in (-2 * jump)..(2 * jump),
        contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 jump source) +
    ((∫ source in (-Real.pi)..(-2 * jump),
        (contourCauchyKernel data.val.1 data.val.2.val.1 0 source -
          contourCauchyKernel data.val.1 data.val.2.val.1 jump source) * (density.val.1 source - density.val.1 0)) +
      ∫ source in (2 * jump)..Real.pi,
        (contourCauchyKernel data.val.1 data.val.2.val.1 0 source -
          contourCauchyKernel data.val.1 data.val.2.val.1 jump source) * (density.val.1 source - density.val.1 0)) +
    (density.val.1 jump - density.val.1 0) *
      ((∫ source in (-Real.pi)..(-2 * jump), contourCauchyKernel data.val.1 data.val.2.val.1 jump source) +
        ∫ source in (2 * jump)..Real.pi, contourCauchyKernel data.val.1 data.val.2.val.1 jump source) -
    ((Real.pi : ℂ) * Complex.I) * (density.val.1 0 - density.val.1 jump) := by
  have domain_ordered : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have zero_near : |(0 : ℝ)| ≤ Real.pi / 4 := by simpa only [abs_zero] using (by positivity : 0 ≤ Real.pi / 4)
  have jump_near : |jump| ≤ Real.pi / 4 := by rw [abs_of_pos jump_pos]; linarith [Real.pi_pos]
  have remainder_integrable : ∀ target ∈ Icc 0 jump, ∀ lower ∈ Icc (-Real.pi) Real.pi,
      ∀ upper ∈ Icc (-Real.pi) Real.pi,
      IntervalIntegrable (contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 target)
        volume lower upper := by
    intro target target_mem lower lower_mem upper upper_mem
    have target_near : |target| ≤ Real.pi / 4 := by
      rw [abs_of_nonneg target_mem.1]
      linarith [target_mem.2, Real.pi_pos]
    apply (banachContourCauchy_density_integrable_fixed_window data density small target_near).mono_set
    apply uIcc_subset_uIcc_iff_mem.mpr
    constructor
    · simpa only [uIcc_of_le domain_ordered] using lower_mem
    · simpa only [uIcc_of_le domain_ordered] using upper_mem
  have first_mem : -Real.pi ∈ Icc (-Real.pi) Real.pi := ⟨le_rfl, domain_ordered⟩
  have second_mem : -2 * jump ∈ Icc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have third_mem : 2 * jump ∈ Icc (-Real.pi) Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have fourth_mem : Real.pi ∈ Icc (-Real.pi) Real.pi := ⟨domain_ordered, le_rfl⟩
  have split_zero := intervalIntegral_three_parts
    (remainder_integrable 0 ⟨le_rfl, jump_pos.le⟩ _ first_mem _ second_mem)
    (remainder_integrable 0 ⟨le_rfl, jump_pos.le⟩ _ second_mem _ third_mem)
    (remainder_integrable 0 ⟨le_rfl, jump_pos.le⟩ _ third_mem _ fourth_mem)
  have split_jump := intervalIntegral_three_parts
    (remainder_integrable jump ⟨jump_pos.le, le_rfl⟩ _ first_mem _ second_mem)
    (remainder_integrable jump ⟨jump_pos.le, le_rfl⟩ _ second_mem _ third_mem)
    (remainder_integrable jump ⟨jump_pos.le, le_rfl⟩ _ third_mem _ fourth_mem)
  have left_zero := banachContourCauchy_intervalIntegrable data small zero_near
    (lower := -Real.pi) (upper := -2 * jump)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl (by linarith))
  have left_jump := banachContourCauchy_intervalIntegrable data small jump_near
    (lower := -Real.pi) (upper := -2 * jump)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inl (by linarith))
  have right_zero := banachContourCauchy_intervalIntegrable data small zero_near
    (lower := 2 * jump) (upper := Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inr (by linarith))
  have right_jump := banachContourCauchy_intervalIntegrable data small jump_near
    (lower := 2 * jump) (upper := Real.pi)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (Or.inr (by linarith))
  have left_identity := contourCauchyDensityRemainder_far_difference_identity density.val.1.continuous left_zero left_jump
  have right_identity := contourCauchyDensityRemainder_far_difference_identity density.val.1.continuous right_zero right_jump
  rw [banachContourCauchyTransform_eq_fixed_window data density 0,
    banachContourCauchyTransform_eq_fixed_window data density jump, split_zero, split_jump]
  linear_combination left_identity + right_identity

theorem norm_cauchy_decomposition_le (nearZero nearJump farLeft farRight densityTerm constantTerm : ℂ) :
    ‖(nearZero - nearJump) + (farLeft + farRight) + densityTerm - constantTerm‖ ≤
      ‖nearZero‖ + ‖nearJump‖ + ‖farLeft‖ + ‖farRight‖ + ‖densityTerm‖ + ‖constantTerm‖ := by
  have first := norm_sub_le ((nearZero - nearJump) + (farLeft + farRight) + densityTerm) constantTerm
  have second := norm_add_le ((nearZero - nearJump) + (farLeft + farRight)) densityTerm
  have third := norm_add_le (nearZero - nearJump) (farLeft + farRight)
  have fourth := norm_sub_le nearZero nearJump
  have fifth := norm_add_le farLeft farRight
  linarith

noncomputable def contourCauchyHolderConstant (data : PeriodicC1HolderHalf) : ℝ :=
  16 * ‖data‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) +
    4 * Real.sqrt 2 * ‖data‖ ^ 2 / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) ^ 2 +
    (4 * ‖data‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖)) * Real.sqrt Real.pi +
    2 * ‖data‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) + Real.pi

set_option maxHeartbeats 1000000 in
theorem banachContourCauchyTransform_holder_local (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {jump : ℝ} (jump_pos : 0 < jump) (jump_small : jump ≤ Real.pi / 8) :
    ‖contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 0 -
      contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 jump‖ ≤
      contourCauchyHolderConstant data * ‖density‖ * Real.sqrt jump := by
  let chord := 2 / (3 * Real.pi) - ‖data - standardCircleBanach‖
  let nearZero := ∫ source in (-2 * jump)..(2 * jump),
    contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 0 source
  let nearJump := ∫ source in (-2 * jump)..(2 * jump),
    contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 jump source
  let farLeft := ∫ source in (-Real.pi)..(-2 * jump),
    (contourCauchyKernel data.val.1 data.val.2.val.1 0 source -
      contourCauchyKernel data.val.1 data.val.2.val.1 jump source) * (density.val.1 source - density.val.1 0)
  let farRight := ∫ source in (2 * jump)..Real.pi,
    (contourCauchyKernel data.val.1 data.val.2.val.1 0 source -
      contourCauchyKernel data.val.1 data.val.2.val.1 jump source) * (density.val.1 source - density.val.1 0)
  let kernelFar := (∫ source in (-Real.pi)..(-2 * jump), contourCauchyKernel data.val.1 data.val.2.val.1 jump source) +
    ∫ source in (2 * jump)..Real.pi, contourCauchyKernel data.val.1 data.val.2.val.1 jump source
  let densityTerm := (density.val.1 jump - density.val.1 0) * kernelFar
  let constantTerm := ((Real.pi : ℂ) * Complex.I) * (density.val.1 0 - density.val.1 jump)
  have near_zero_bound : ‖nearZero‖ ≤ (8 * (‖density‖ * ‖data‖ / chord)) * Real.sqrt jump :=
    banachContourCauchy_density_near_bound data density small jump_pos jump_small ⟨le_rfl, jump_pos.le⟩
  have near_jump_bound : ‖nearJump‖ ≤ (8 * (‖density‖ * ‖data‖ / chord)) * Real.sqrt jump :=
    banachContourCauchy_density_near_bound data density small jump_pos jump_small ⟨jump_pos.le, le_rfl⟩
  have far_left_bound : ‖farLeft‖ ≤ (2 * ‖data‖ ^ 2 * ‖density‖ / chord ^ 2) * Real.sqrt (2 * jump) :=
    banachContourCauchy_density_far_left_bound data density small jump_pos jump_small
  have far_right_bound : ‖farRight‖ ≤ (2 * ‖data‖ ^ 2 * ‖density‖ / chord ^ 2) * Real.sqrt (2 * jump) :=
    banachContourCauchy_density_far_right_bound data density small jump_pos jump_small
  have kernel_far_bound : ‖kernelFar‖ ≤ (4 * ‖data‖ / chord) * Real.sqrt Real.pi + 2 * ‖data‖ / chord :=
    banachContourCauchy_offCenter_far_bound data small jump_pos jump_small
  have density_difference : ‖density.val.1 jump - density.val.1 0‖ ≤ ‖density‖ * Real.sqrt jump := by
    simpa only [sub_zero, abs_of_pos jump_pos] using PeriodicHolderHalf.holder_bound density jump 0
  have density_term_bound : ‖densityTerm‖ ≤ (‖density‖ * Real.sqrt jump) *
      ((4 * ‖data‖ / chord) * Real.sqrt Real.pi + 2 * ‖data‖ / chord) := by
    change ‖(density.val.1 jump - density.val.1 0) * kernelFar‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul density_difference kernel_far_bound (norm_nonneg _) (by positivity)
  have constant_term_bound : ‖constantTerm‖ ≤ Real.pi * ‖density‖ * Real.sqrt jump := by
    change ‖((Real.pi : ℂ) * Complex.I) * (density.val.1 0 - density.val.1 jump)‖ ≤ _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_I, mul_one, norm_sub_rev (density.val.1 0) (density.val.1 jump)]
    exact (mul_le_mul_of_nonneg_left density_difference Real.pi_pos.le).trans_eq (by ring)
  have identity := banachContourCauchyTransform_difference_decomposition data density small jump_pos jump_small
  change _ = (nearZero - nearJump) + (farLeft + farRight) + densityTerm - constantTerm at identity
  rw [identity]
  calc
    _ ≤ ‖nearZero‖ + ‖nearJump‖ + ‖farLeft‖ + ‖farRight‖ + ‖densityTerm‖ + ‖constantTerm‖ :=
      norm_cauchy_decomposition_le _ _ _ _ _ _
    _ ≤ 2 * (8 * (‖density‖ * ‖data‖ / chord)) * Real.sqrt jump +
        2 * (2 * ‖data‖ ^ 2 * ‖density‖ / chord ^ 2) * Real.sqrt (2 * jump) +
        (‖density‖ * Real.sqrt jump) * ((4 * ‖data‖ / chord) * Real.sqrt Real.pi + 2 * ‖data‖ / chord) +
        Real.pi * ‖density‖ * Real.sqrt jump := by linarith
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp only [contourCauchyHolderConstant, chord]
      ring

end EulerNonuniqueness.Paper
