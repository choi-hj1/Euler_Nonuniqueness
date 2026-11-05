import EulerNonuniqueness.Section3.ContourCauchyLipschitzLocal
import EulerNonuniqueness.Section3.HolderNormCharacterization

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem contourCauchyParameterHolderLocalConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourCauchyParameterHolderLocalConstant radius := by
  have size_nonneg := contourKernelParameterSizeConstant_nonneg radius_nonneg radius_small
  have smooth_nonneg := contourKernelParameterSmoothConstant_nonneg radius_nonneg
  unfold contourCauchyParameterHolderLocalConstant
  positivity

theorem contourCauchyTransform_parameter_holder_near_ordered (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius left right : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius)
    (ordered : left < right) (nearby : right - left ≤ Real.pi / 8) :
    ‖(contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 left -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 left) -
      (contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 right -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 right)‖ ≤
      contourCauchyParameterHolderLocalConstant radius * ‖first - second‖ * ‖density‖ * Real.sqrt (right - left) := by
  have actual := contourCauchyTransform_parameter_holder_local
    (normalizedContourShift left first) (normalizedContourShift left second) (holderLabelShift left density)
    radius_nonneg radius_small (by rwa [normalizedContourShift_distance_circle])
    (by rwa [normalizedContourShift_distance_circle]) (sub_pos.mpr ordered) nearby
  simp_rw [contourCauchyTransform_normalized_shift] at actual
  rw [← normalizedContourShift_sub, normalizedContourShift_norm, holderLabelShift_norm] at actual
  simpa only [zero_add, sub_add_cancel] using actual

theorem contourCauchyTransform_parameter_holder_near (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius left right : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius) (nearby : |left - right| ≤ Real.pi / 8) :
    ‖(contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 left -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 left) -
      (contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 right -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 right)‖ ≤
      contourCauchyParameterHolderLocalConstant radius * ‖first - second‖ * ‖density‖ * Real.sqrt |left - right| := by
  rcases lt_trichotomy left right with ordered | equal | ordered
  · have actual := contourCauchyTransform_parameter_holder_near_ordered first second density radius_nonneg radius_small
      first_near second_near ordered (by simpa only [abs_of_neg (sub_neg.mpr ordered), neg_sub] using nearby)
    simpa only [abs_of_neg (sub_neg.mpr ordered), neg_sub] using actual
  · subst right
    simp
  · have actual := contourCauchyTransform_parameter_holder_near_ordered first second density radius_nonneg radius_small
      first_near second_near ordered (by simpa only [abs_of_pos (sub_pos.mpr ordered)] using nearby)
    simpa only [norm_sub_rev, abs_of_pos (sub_pos.mpr ordered)] using actual

noncomputable def contourCauchyParameterSupConstant (radius : ℝ) : ℝ :=
  4 * contourKernelParameterSizeConstant radius * Real.sqrt (2 * Real.pi)

theorem contourCauchyParameterSupConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourCauchyParameterSupConstant radius := by
  have nonnegative := contourKernelParameterSizeConstant_nonneg radius_nonneg radius_small
  unfold contourCauchyParameterSupConstant
  positivity

set_option maxHeartbeats 1000000 in
theorem contourCauchyTransform_parameter_norm_bound (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius) (target : ℝ) :
    ‖contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 target -
      contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 target‖ ≤
      contourCauchyParameterSupConstant radius * ‖first - second‖ * ‖density‖ := by
  have size_nonneg := contourKernelParameterSizeConstant_nonneg radius_nonneg radius_small
  have identity : contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 target -
      contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 target =
      ∫ source in (target - Real.pi)..(target + Real.pi),
        contourCauchyDensityRemainder first.val.1 first.val.2.val.1 density.val.1 target source -
          contourCauchyDensityRemainder second.val.1 second.val.2.val.1 density.val.1 target source := by
    unfold contourCauchyTransform
    rw [intervalIntegral.integral_sub
      (banachContourCauchy_density_integrable_centered first density (first_near.trans_lt radius_small) target)
      (banachContourCauchy_density_integrable_centered second density (second_near.trans_lt radius_small) target)]
    ring
  rw [identity]
  have estimate := norm_setIntegral_weakSingular_near (radius := 2 * Real.pi) (center := target)
    (domain := Ioc (target - Real.pi) (target + Real.pi)) (by positivity)
    (show 0 ≤ ‖density‖ * (‖first - second‖ * contourKernelParameterSizeConstant radius) by positivity)
    measurableSet_Ioc (fun source membership => by constructor <;> linarith [membership.1, membership.2, Real.pi_pos])
    (fun source membership => contourCauchyDensityRemainder_parameter_point_bound first second density
      radius_nonneg radius_small first_near second_near (by
        rw [abs_le]
        constructor <;> linarith [membership.1, membership.2, Real.pi_pos]))
  rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : target - Real.pi ≤ target + Real.pi)] at estimate
  convert estimate using 1 <;> unfold contourCauchyParameterSupConstant <;> ring

noncomputable def contourCauchyParameterGlobalHolderConstant (radius : ℝ) : ℝ :=
  max (contourCauchyParameterHolderLocalConstant radius)
    (2 * contourCauchyParameterSupConstant radius / Real.sqrt (Real.pi / 8))

theorem contourCauchyParameterGlobalHolderConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourCauchyParameterGlobalHolderConstant radius :=
  (contourCauchyParameterHolderLocalConstant_nonneg radius_nonneg radius_small).trans (le_max_left _ _)

theorem contourCauchyTransform_parameter_holder (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius) (left right : ℝ) :
    ‖(contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 left -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 left) -
      (contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 right -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 right)‖ ≤
      contourCauchyParameterGlobalHolderConstant radius * ‖first - second‖ * ‖density‖ * Real.sqrt |left - right| := by
  by_cases nearby : |left - right| ≤ Real.pi / 8
  · exact (contourCauchyTransform_parameter_holder_near first second density radius_nonneg radius_small
      first_near second_near nearby).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (norm_nonneg _)) (Real.sqrt_nonneg _))
  have root_pos : 0 < Real.sqrt (Real.pi / 8) := Real.sqrt_pos.mpr (by positivity)
  have root_le : Real.sqrt (Real.pi / 8) ≤ Real.sqrt |left - right| := Real.sqrt_le_sqrt (le_of_lt (lt_of_not_ge nearby))
  have sup_nonneg := contourCauchyParameterSupConstant_nonneg radius_nonneg radius_small
  calc
    _ ≤ ‖contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 left -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 left‖ +
      ‖contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 right -
        contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 right‖ := norm_sub_le _ _
    _ ≤ 2 * contourCauchyParameterSupConstant radius * ‖first - second‖ * ‖density‖ := by
      linarith [contourCauchyTransform_parameter_norm_bound first second density radius_nonneg radius_small first_near second_near left,
        contourCauchyTransform_parameter_norm_bound first second density radius_nonneg radius_small first_near second_near right]
    _ = (2 * contourCauchyParameterSupConstant radius / Real.sqrt (Real.pi / 8)) * ‖first - second‖ * ‖density‖ * Real.sqrt (Real.pi / 8) := by
      field_simp
      ring
    _ ≤ (2 * contourCauchyParameterSupConstant radius / Real.sqrt (Real.pi / 8)) * ‖first - second‖ * ‖density‖ * Real.sqrt |left - right| :=
      mul_le_mul_of_nonneg_left root_le (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) (norm_nonneg _)) (Real.sqrt_nonneg _)

noncomputable def contourCauchyParameterOperatorConstant (radius : ℝ) : ℝ :=
  max (contourCauchyParameterSupConstant radius) (contourCauchyParameterGlobalHolderConstant radius)

theorem contourCauchyOperator_parameter_norm_bound (first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius)
    (second_near : ‖second - standardCircleBanach‖ ≤ radius) :
    ‖contourCauchyOperator first (first_near.trans_lt radius_small) density -
      contourCauchyOperator second (second_near.trans_lt radius_small) density‖ ≤
      contourCauchyParameterOperatorConstant radius * ‖first - second‖ * ‖density‖ := by
  have constant_nonneg : 0 ≤ contourCauchyParameterOperatorConstant radius :=
    (contourCauchyParameterSupConstant_nonneg radius_nonneg radius_small).trans (le_max_left _ _)
  apply PeriodicHolderHalf.norm_le_of_bounds _ (by positivity)
  · intro label
    change ‖contourCauchyTransform first.val.1 first.val.2.val.1 density.val.1 label -
      contourCauchyTransform second.val.1 second.val.2.val.1 density.val.1 label‖ ≤ _
    exact (contourCauchyTransform_parameter_norm_bound first second density radius_nonneg radius_small first_near second_near label).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (norm_nonneg _))
  · intro left right
    exact (contourCauchyTransform_parameter_holder first second density radius_nonneg radius_small first_near second_near left right).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) (norm_nonneg _)) (Real.sqrt_nonneg _))

end EulerNonuniqueness.Paper
