import EulerNonuniqueness.Section3.ContourKernelVariation
import EulerNonuniqueness.Section3.ComplexHolderInstances

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def contourCauchyKernelQuadratic (data first second : PeriodicC1HolderHalf)
    (target source : ℝ) : ℂ :=
  -(1 / 2 : ℂ) *
    (((first.val.1 target - first.val.1 source) /
        (data.val.1 target - data.val.1 source)) *
        contourCauchyKernelVariation data second target source +
      ((second.val.1 target - second.val.1 source) /
        (data.val.1 target - data.val.1 source)) *
        contourCauchyKernelVariation data first target source)

theorem contourCauchyKernelQuadratic_symm (data first second : PeriodicC1HolderHalf)
    (target source : ℝ) :
    contourCauchyKernelQuadratic data first second target source =
      contourCauchyKernelQuadratic data second first target source := by
  unfold contourCauchyKernelQuadratic
  rw [add_comm]

theorem contourCauchyKernelQuadratic_diagonal (data direction : PeriodicC1HolderHalf)
    (target source : ℝ) :
    contourCauchyKernelQuadratic data direction direction target source =
      -((direction.val.1 target - direction.val.1 source) /
        (data.val.1 target - data.val.1 source)) *
        contourCauchyKernelVariation data direction target source := by
  unfold contourCauchyKernelQuadratic
  ring

theorem contourCauchyKernelQuadratic_add_left (data first second third : PeriodicC1HolderHalf)
    (target source : ℝ) :
    contourCauchyKernelQuadratic data (first + second) third target source =
      contourCauchyKernelQuadratic data first third target source +
        contourCauchyKernelQuadratic data second third target source := by
  unfold contourCauchyKernelQuadratic contourCauchyKernelVariation
  have value (label : ℝ) : (first + second).val.1 label =
      first.val.1 label + second.val.1 label := rfl
  have tangent : (first + second).val.2.val.1 source =
      first.val.2.val.1 source + second.val.2.val.1 source := rfl
  rw [value target, value source, tangent]
  ring

theorem contourCauchyKernelQuadratic_smul_left (data first second : PeriodicC1HolderHalf)
    (scalar : ℂ) (target source : ℝ) :
    contourCauchyKernelQuadratic data (scalar • first) second target source =
      scalar * contourCauchyKernelQuadratic data first second target source := by
  unfold contourCauchyKernelQuadratic contourCauchyKernelVariation
  have value (label : ℝ) : (scalar • first).val.1 label = scalar * first.val.1 label := rfl
  have tangent : (scalar • first).val.2.val.1 source = scalar * first.val.2.val.1 source := rfl
  rw [value target, value source, tangent]
  ring

theorem contourCauchyKernelQuadratic_taylor_identity (data direction : PeriodicC1HolderHalf)
    (parameter : ℂ) {target source : ℝ}
    (separated : data.val.1 target - data.val.1 source ≠ 0)
    (perturbed_separated : data.val.1 target - data.val.1 source +
      parameter * (direction.val.1 target - direction.val.1 source) ≠ 0) :
    (data.val.2.val.1 source + parameter * direction.val.2.val.1 source) /
        (data.val.1 target - data.val.1 source +
          parameter * (direction.val.1 target - direction.val.1 source)) -
      data.val.2.val.1 source / (data.val.1 target - data.val.1 source) -
      parameter * contourCauchyKernelVariation data direction target source =
    parameter ^ 2 * contourCauchyKernelQuadratic data direction direction target source *
      ((data.val.1 target - data.val.1 source) /
        (data.val.1 target - data.val.1 source +
          parameter * (direction.val.1 target - direction.val.1 source))) := by
  rw [contourCauchyKernelQuadratic_diagonal]
  unfold contourCauchyKernelVariation
  generalize difference_eq : data.val.1 target - data.val.1 source = difference at *
  generalize increment_eq : direction.val.1 target - direction.val.1 source = increment at *
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  field_simp [separated, perturbed_separated]
  <;> ring

theorem contourCauchy_increment_ratio_bound (data direction : PeriodicC1HolderHalf)
    {target source chord : ℝ} (distinct : source ≠ target) (chord_positive : 0 < chord)
    (lower : chord * |target - source| ≤ ‖data.val.1 target - data.val.1 source‖) :
    ‖(direction.val.1 target - direction.val.1 source) /
      (data.val.1 target - data.val.1 source)‖ ≤ ‖direction‖ / chord := by
  have distance_positive : 0 < |target - source| :=
    abs_pos.mpr (sub_ne_zero.mpr distinct.symm)
  have denominator_positive : 0 < ‖data.val.1 target - data.val.1 source‖ :=
    (mul_pos chord_positive distance_positive).trans_le lower
  rw [norm_div]
  calc
    _ ≤ (‖direction‖ * |target - source|) /
        ‖data.val.1 target - data.val.1 source‖ :=
      div_le_div_of_nonneg_right
        (PeriodicC1HolderHalf.lipschitz_bound direction target source) denominator_positive.le
    _ ≤ (‖direction‖ * |target - source|) / (chord * |target - source|) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) lower
    _ = _ := by field_simp; ring

theorem contourCauchyKernelQuadratic_weak_bound (data first second : PeriodicC1HolderHalf)
    {target source chord : ℝ} (distinct : source ≠ target) (chord_positive : 0 < chord)
    (lower : chord * |target - source| ≤ ‖data.val.1 target - data.val.1 source‖) :
    ‖contourCauchyKernelQuadratic data first second target source‖ ≤
      2 * ‖data‖ * ‖first‖ * ‖second‖ /
        (chord ^ 3 * Real.sqrt |target - source|) := by
  have first_ratio := contourCauchy_increment_ratio_bound data first distinct chord_positive lower
  have second_ratio := contourCauchy_increment_ratio_bound data second distinct chord_positive lower
  have first_variation := contourCauchyKernelVariation_weak_bound data first distinct chord_positive lower
  have second_variation := contourCauchyKernelVariation_weak_bound data second distinct chord_positive lower
  have first_product := mul_le_mul first_ratio second_variation (norm_nonneg _)
    (div_nonneg (norm_nonneg first) chord_positive.le)
  have second_product := mul_le_mul second_ratio first_variation (norm_nonneg _)
    (div_nonneg (norm_nonneg second) chord_positive.le)
  unfold contourCauchyKernelQuadratic
  rw [norm_mul, norm_neg]
  have scalar_norm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [scalar_norm]
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
  simp only [norm_mul]
  apply (mul_le_mul_of_nonneg_left (add_le_add first_product second_product)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq
  field_simp
  <;> ring

end

end EulerNonuniqueness.Paper
