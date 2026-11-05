import EulerNonuniqueness.Section3.ContourCauchyHolder

open Set
open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def normalizedContourShift (offset : ℝ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf := by
  let rotation := (standardCircle offset)⁻¹
  have rotation_norm : ‖rotation‖ = 1 := by simp [rotation, norm_inv, standardCircle_norm]
  have function_continuous : Continuous (fun source => rotation * data.val.1 (source + offset)) :=
    continuous_const.mul (data.val.1.continuous.comp (continuous_id.add continuous_const))
  have tangent_continuous : Continuous (fun source => rotation * data.val.2.val.1 (source + offset)) :=
    continuous_const.mul (data.val.2.val.1.continuous.comp (continuous_id.add continuous_const))
  apply PeriodicC1HolderHalf.ofFunctions
    (fun source => rotation * data.val.1 (source + offset))
    (fun source => rotation * data.val.2.val.1 (source + offset))
    function_continuous tangent_continuous ‖data‖ ‖data‖ ‖data‖
  · intro label
    rw [norm_mul, rotation_norm, one_mul]
    exact PeriodicC1HolderHalf.value_bound data (label + offset)
  · intro label
    rw [norm_mul, rotation_norm, one_mul]
    exact PeriodicC1HolderHalf.speed_bound data (label + offset)
  · intro first second
    rw [← mul_sub, norm_mul, rotation_norm, one_mul]
    simpa only [add_sub_add_right_eq_sub] using
      PeriodicC1HolderHalf.derivative_holder_bound data (first + offset) (second + offset)
  · intro label
    have actual := ((PeriodicC1HolderHalf.hasDerivAt data (label + offset)).scomp label
      ((hasDerivAt_id label).add_const offset)).const_mul rotation
    simpa only [Function.comp_apply, id_eq, one_smul] using actual
  · intro label
    dsimp only
    have identity : label + 2 * Real.pi + offset = label + offset + 2 * Real.pi := by ring
    rw [identity, PeriodicC1HolderHalf.periodic data (label + offset)]
  · intro label
    dsimp only
    have identity : label + 2 * Real.pi + offset = label + offset + 2 * Real.pi := by ring
    rw [identity, PeriodicHolderHalf.periodic data.val.2 (label + offset)]

theorem normalizedContourShift_value (offset : ℝ) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (normalizedContourShift offset data).val.1 label =
      (standardCircle offset)⁻¹ * data.val.1 (label + offset) := rfl

theorem normalizedContourShift_tangent (offset : ℝ) (data : PeriodicC1HolderHalf) (label : ℝ) :
    (normalizedContourShift offset data).val.2.val.1 label =
      (standardCircle offset)⁻¹ * data.val.2.val.1 (label + offset) := rfl

set_option maxHeartbeats 1000000 in
theorem normalizedContourShift_norm_le (offset : ℝ) (data : PeriodicC1HolderHalf) :
    ‖normalizedContourShift offset data‖ ≤ ‖data‖ := by
  unfold normalizedContourShift
  refine (PeriodicC1HolderHalf.ofFunctions_norm_bound _ _ _ _
    (norm_nonneg data) (norm_nonneg data) (norm_nonneg data) _ _ _ _ _ _).trans ?_
  simp only [max_self]
  exact le_rfl

theorem normalizedContourShift_sub (offset : ℝ) (first second : PeriodicC1HolderHalf) :
    normalizedContourShift offset (first - second) = normalizedContourShift offset first - normalizedContourShift offset second := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change _ * (first.val.1 (label + offset) - second.val.1 (label + offset)) =
    _ * first.val.1 (label + offset) - _ * second.val.1 (label + offset)
  ring

theorem normalizedContourShift_circle (offset : ℝ) :
    normalizedContourShift offset standardCircleBanach = standardCircleBanach := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (standardCircle offset)⁻¹ * standardCircle (label + offset) = standardCircle label
  rw [standardCircle_add]
  have nonzero : standardCircle offset ≠ 0 := by simp [standardCircle, Complex.exp_ne_zero]
  field_simp

theorem normalizedContourShift_inverse (offset : ℝ) (data : PeriodicC1HolderHalf) :
    normalizedContourShift (-offset) (normalizedContourShift offset data) = data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [normalizedContourShift_value, normalizedContourShift_value]
  have circle_product : standardCircle (-offset) * standardCircle offset = 1 := by
    rw [← standardCircle_add, neg_add_cancel]
    simp [standardCircle]
  have rotation_product : (standardCircle (-offset))⁻¹ * (standardCircle offset)⁻¹ = 1 := by
    rw [← mul_inv_rev, mul_comm, circle_product, inv_one]
  rw [← mul_assoc, rotation_product, one_mul]
  congr 1
  ring

theorem normalizedContourShift_norm (offset : ℝ) (data : PeriodicC1HolderHalf) :
    ‖normalizedContourShift offset data‖ = ‖data‖ := by
  apply le_antisymm (normalizedContourShift_norm_le offset data)
  have inverse_bound := normalizedContourShift_norm_le (-offset) (normalizedContourShift offset data)
  rwa [normalizedContourShift_inverse] at inverse_bound

theorem normalizedContourShift_distance_circle (offset : ℝ) (data : PeriodicC1HolderHalf) :
    ‖normalizedContourShift offset data - standardCircleBanach‖ = ‖data - standardCircleBanach‖ := by
  calc
    _ = ‖normalizedContourShift offset data - normalizedContourShift offset standardCircleBanach‖ := by
      rw [normalizedContourShift_circle]
    _ = ‖normalizedContourShift offset (data - standardCircleBanach)‖ := by
      rw [normalizedContourShift_sub]
    _ = _ := normalizedContourShift_norm _ _

def holderLabelShift (offset : ℝ) (density : PeriodicHolderHalf) : PeriodicHolderHalf := by
  apply PeriodicHolderHalf.ofFunction (fun source => density.val.1 (source + offset))
    (density.val.1.continuous.comp (continuous_id.add continuous_const)) ‖density‖ ‖density‖
  · intro label
    exact PeriodicHolderHalf.value_bound density (label + offset)
  · intro first second
    simpa only [add_sub_add_right_eq_sub] using
      PeriodicHolderHalf.holder_bound density (first + offset) (second + offset)
  · intro label
    dsimp only
    have identity : label + 2 * Real.pi + offset = label + offset + 2 * Real.pi := by ring
    rw [identity, PeriodicHolderHalf.periodic density (label + offset)]

theorem holderLabelShift_value (offset : ℝ) (density : PeriodicHolderHalf) (label : ℝ) :
    (holderLabelShift offset density).val.1 label = density.val.1 (label + offset) := rfl

theorem holderLabelShift_norm_le (offset : ℝ) (density : PeriodicHolderHalf) :
    ‖holderLabelShift offset density‖ ≤ ‖density‖ := by
  unfold holderLabelShift
  refine (PeriodicHolderHalf.ofFunction_norm_bound _ _
    (norm_nonneg density) (norm_nonneg density) _ _ _).trans ?_
  simp only [max_self]
  exact le_rfl

theorem holderLabelShift_inverse (offset : ℝ) (density : PeriodicHolderHalf) :
    holderLabelShift (-offset) (holderLabelShift offset density) = density := by
  apply PeriodicHolderHalf.ext_value
  intro label
  rw [holderLabelShift_value, holderLabelShift_value]
  congr 1
  ring

theorem holderLabelShift_norm (offset : ℝ) (density : PeriodicHolderHalf) :
    ‖holderLabelShift offset density‖ = ‖density‖ := by
  apply le_antisymm (holderLabelShift_norm_le offset density)
  have bound := holderLabelShift_norm_le (-offset) (holderLabelShift offset density)
  rwa [holderLabelShift_inverse] at bound

theorem contourCauchyTransform_normalized_shift (offset : ℝ) (data : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) (target : ℝ) :
    contourCauchyTransform (normalizedContourShift offset data).val.1
      (normalizedContourShift offset data).val.2.val.1 (holderLabelShift offset density).val.1 target =
    contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 (target + offset) := by
  have rotation_ne : (standardCircle offset)⁻¹ ≠ 0 := by simp [standardCircle, Complex.exp_ne_zero]
  have remainder_identity : ∀ source : ℝ,
      contourCauchyDensityRemainder (normalizedContourShift offset data).val.1
        (normalizedContourShift offset data).val.2.val.1 (holderLabelShift offset density).val.1 target source =
      contourCauchyDensityRemainder data.val.1 data.val.2.val.1 density.val.1 (target + offset) (source + offset) := by
    intro source
    unfold contourCauchyDensityRemainder
    rw [holderLabelShift_value, holderLabelShift_value, normalizedContourShift_tangent,
      normalizedContourShift_value, normalizedContourShift_value, ← mul_sub,
      mul_div_assoc, mul_div_mul_left _ _ rotation_ne, ← mul_div_assoc]
  unfold contourCauchyTransform
  simp_rw [remainder_identity]
  rw [intervalIntegral.integral_comp_add_right, holderLabelShift_value]
  have lower : target - Real.pi + offset = target + offset - Real.pi := by ring
  have upper : target + Real.pi + offset = target + offset + Real.pi := by ring
  rw [lower, upper]

theorem contourCauchyHolderConstant_normalized_shift (offset : ℝ) (data : PeriodicC1HolderHalf) :
    contourCauchyHolderConstant (normalizedContourShift offset data) = contourCauchyHolderConstant data := by
  unfold contourCauchyHolderConstant
  rw [normalizedContourShift_norm, normalizedContourShift_distance_circle]

end

end EulerNonuniqueness.Paper
