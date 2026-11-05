import EulerNonuniqueness.Section3.ContourLabelShift

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

theorem contourCauchyHolderConstant_nonneg (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    0 ≤ contourCauchyHolderConstant data := by
  have positive := sub_pos.mpr (small.trans_le (min_le_right _ _))
  unfold contourCauchyHolderConstant
  positivity

set_option maxHeartbeats 1000000 in
theorem banachContourCauchyTransform_holder_near_ordered (data : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {first second : ℝ} (ordered : first < second) (nearby : second - first ≤ Real.pi / 8) :
    ‖contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 first -
      contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 second‖ ≤
      contourCauchyHolderConstant data * ‖density‖ * Real.sqrt (second - first) := by
  have shifted_small : ‖normalizedContourShift first data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    rwa [normalizedContourShift_distance_circle]
  have actual := banachContourCauchyTransform_holder_local (normalizedContourShift first data)
    (holderLabelShift first density) shifted_small (sub_pos.mpr ordered) nearby
  rw [contourCauchyHolderConstant_normalized_shift, holderLabelShift_norm,
    contourCauchyTransform_normalized_shift, contourCauchyTransform_normalized_shift] at actual
  simpa only [zero_add, sub_add_cancel] using actual

theorem banachContourCauchyTransform_holder_near (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    {first second : ℝ} (nearby : |first - second| ≤ Real.pi / 8) :
    ‖contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 first -
      contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 second‖ ≤
      contourCauchyHolderConstant data * ‖density‖ * Real.sqrt |first - second| := by
  rcases lt_trichotomy first second with ordered | equal | ordered
  · have actual := banachContourCauchyTransform_holder_near_ordered data density small ordered
      (by simpa only [abs_of_neg (sub_neg.mpr ordered), neg_sub] using nearby)
    simpa only [abs_of_neg (sub_neg.mpr ordered), neg_sub] using actual
  · subst second
    simp
  · have actual := banachContourCauchyTransform_holder_near_ordered data density small ordered
      (by simpa only [abs_of_pos (sub_pos.mpr ordered)] using nearby)
    simpa only [norm_sub_rev, abs_of_pos (sub_pos.mpr ordered)] using actual

noncomputable def contourCauchySupConstant (data : PeriodicC1HolderHalf) : ℝ :=
  (4 * ‖data‖ / (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖)) * Real.sqrt (2 * Real.pi) + Real.pi

theorem contourCauchySupConstant_nonneg (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    0 ≤ contourCauchySupConstant data := by
  have positive := sub_pos.mpr (small.trans_le (min_le_right _ _))
  unfold contourCauchySupConstant
  positivity

set_option maxHeartbeats 1000000 in
theorem banachContourCauchyTransform_norm_bound (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    ‖contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 target‖ ≤
      contourCauchySupConstant data * ‖density‖ := by
  have positive := sub_pos.mpr (small.trans_le (min_le_right _ _))
  have estimate := contourCauchyDensityRemainder_near_bound (radius := 2 * Real.pi)
    (domain := Ioc (target - Real.pi) (target + Real.pi)) (by positivity)
    (norm_nonneg density) (norm_nonneg data) positive measurableSet_Ioc
    (fun source membership => by constructor <;> linarith [membership.1, membership.2, Real.pi_pos])
    (fun source _ => PeriodicHolderHalf.holder_bound density source target)
    (fun source _ => PeriodicC1HolderHalf.speed_bound data source)
    (fun source membership => by
      apply PeriodicC1HolderHalf.chord_bound_extended data
      rw [abs_le]
      constructor <;> linarith [membership.1, membership.2, Real.pi_pos])
  rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : target - Real.pi ≤ target + Real.pi)] at estimate
  have constant_bound : ‖(Real.pi : ℂ) * Complex.I * density.val.1 target‖ ≤ Real.pi * ‖density‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    exact mul_le_mul_of_nonneg_left (PeriodicHolderHalf.value_bound density target) Real.pi_pos.le
  unfold contourCauchyTransform
  apply (norm_sub_le _ _).trans ((add_le_add estimate constant_bound).trans_eq ?_)
  unfold contourCauchySupConstant
  ring

noncomputable def contourCauchyGlobalHolderConstant (data : PeriodicC1HolderHalf) : ℝ :=
  max (contourCauchyHolderConstant data) (2 * contourCauchySupConstant data / Real.sqrt (Real.pi / 8))

theorem contourCauchyGlobalHolderConstant_nonneg (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    0 ≤ contourCauchyGlobalHolderConstant data :=
  (contourCauchyHolderConstant_nonneg data small).trans (le_max_left _ _)

theorem banachContourCauchyTransform_holder (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (first second : ℝ) :
    ‖contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 first -
      contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 second‖ ≤
      contourCauchyGlobalHolderConstant data * ‖density‖ * Real.sqrt |first - second| := by
  by_cases nearby : |first - second| ≤ Real.pi / 8
  · exact (banachContourCauchyTransform_holder_near data density small nearby).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg density))
        (Real.sqrt_nonneg _))
  have root_pos : 0 < Real.sqrt (Real.pi / 8) := Real.sqrt_pos.mpr (by positivity)
  have root_le : Real.sqrt (Real.pi / 8) ≤ Real.sqrt |first - second| :=
    Real.sqrt_le_sqrt (le_of_lt (lt_of_not_ge nearby))
  have sup_nonneg := contourCauchySupConstant_nonneg data small
  calc
    _ ≤ ‖contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 first‖ +
        ‖contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 second‖ := norm_sub_le _ _
    _ ≤ 2 * contourCauchySupConstant data * ‖density‖ := by
      linarith [banachContourCauchyTransform_norm_bound data density small first,
        banachContourCauchyTransform_norm_bound data density small second]
    _ = (2 * contourCauchySupConstant data / Real.sqrt (Real.pi / 8)) * ‖density‖ * Real.sqrt (Real.pi / 8) := by
      field_simp
      ring
    _ ≤ (2 * contourCauchySupConstant data / Real.sqrt (Real.pi / 8)) * ‖density‖ * Real.sqrt |first - second| :=
      mul_le_mul_of_nonneg_left root_le (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg density)) (Real.sqrt_nonneg _)

theorem continuous_of_sqrt_norm_bound {function : ℝ → ℂ} {constant : ℝ}
    (constant_nonneg : 0 ≤ constant)
    (estimate : ∀ first second : ℝ, ‖function first - function second‖ ≤ constant * Real.sqrt |first - second|) :
    Continuous function := by
  apply continuous_iff_continuousAt.mpr
  intro label
  apply Metric.continuousAt_iff.mpr
  intro epsilon epsilon_pos
  let quotient := epsilon / (constant + 1)
  have denominator_pos : 0 < constant + 1 := by linarith
  have quotient_pos : 0 < quotient := div_pos epsilon_pos denominator_pos
  refine ⟨quotient ^ 2, by positivity, ?_⟩
  intro source distance
  rw [Real.dist_eq] at distance
  have root_lt : Real.sqrt |source - label| < quotient :=
    (Real.sqrt_lt (abs_nonneg _) quotient_pos.le).mpr distance
  rw [dist_eq_norm]
  calc
    _ ≤ constant * Real.sqrt |source - label| := estimate source label
    _ ≤ (constant + 1) * Real.sqrt |source - label| :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    _ < (constant + 1) * quotient := mul_lt_mul_of_pos_left root_lt denominator_pos
    _ = epsilon := by dsimp only [quotient]; field_simp

theorem banachContourCauchyTransform_continuous (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    Continuous (contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1) :=
  continuous_of_sqrt_norm_bound
    (mul_nonneg (contourCauchyGlobalHolderConstant_nonneg data small) (norm_nonneg density))
    (banachContourCauchyTransform_holder data density small)

theorem banachContourCauchyTransform_periodic (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf) :
    Function.Periodic (contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1) (2 * Real.pi) := by
  intro label
  rw [banachContourCauchyTransform_eq_fixed_window data density (label + 2 * Real.pi),
    banachContourCauchyTransform_eq_fixed_window data density label]
  unfold contourCauchyDensityRemainder
  rw [PeriodicC1HolderHalf.periodic data label, PeriodicHolderHalf.periodic density label]

noncomputable def contourCauchyOperator (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (density : PeriodicHolderHalf) : PeriodicHolderHalf :=
  PeriodicHolderHalf.ofFunction (contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1)
    (banachContourCauchyTransform_continuous data density small)
    (contourCauchySupConstant data * ‖density‖) (contourCauchyGlobalHolderConstant data * ‖density‖)
    (banachContourCauchyTransform_norm_bound data density small)
    (banachContourCauchyTransform_holder data density small) (banachContourCauchyTransform_periodic data density)

theorem contourCauchyOperator_value (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (density : PeriodicHolderHalf) (label : ℝ) :
    (contourCauchyOperator data small density).val.1 label =
      contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1 label := rfl

theorem contourCauchyOperator_norm_bound (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (density : PeriodicHolderHalf) :
    ‖contourCauchyOperator data small density‖ ≤
      max (contourCauchySupConstant data) (contourCauchyGlobalHolderConstant data) * ‖density‖ := by
  unfold contourCauchyOperator
  have bound := PeriodicHolderHalf.ofFunction_norm_bound
    (contourCauchyTransform data.val.1 data.val.2.val.1 density.val.1)
    (banachContourCauchyTransform_continuous data density small)
    (mul_nonneg (contourCauchySupConstant_nonneg data small) (norm_nonneg density))
    (mul_nonneg (contourCauchyGlobalHolderConstant_nonneg data small) (norm_nonneg density))
    (banachContourCauchyTransform_norm_bound data density small)
    (banachContourCauchyTransform_holder data density small) (banachContourCauchyTransform_periodic data density)
  exact bound.trans_eq (max_mul_of_nonneg _ _ (norm_nonneg density)).symm

end EulerNonuniqueness.Paper
