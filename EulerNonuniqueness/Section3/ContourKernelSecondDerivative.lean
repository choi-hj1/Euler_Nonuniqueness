import EulerNonuniqueness.Section3.ContourKernelQuadratic

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 800000

theorem contourCauchyKernelVariation_hasDerivAt_mixed_parameter
    (data first second : PeriodicC1HolderHalf)
    {target source : ℝ} (separated : data.val.1 target - data.val.1 source ≠ 0) :
    HasDerivAt (fun parameter : ℂ =>
      first.val.2.val.1 source /
          (data.val.1 target - data.val.1 source +
            parameter * (second.val.1 target - second.val.1 source)) -
        (data.val.2.val.1 source + parameter * second.val.2.val.1 source) *
          (first.val.1 target - first.val.1 source) /
          (data.val.1 target - data.val.1 source +
            parameter * (second.val.1 target - second.val.1 source)) ^ 2)
      (2 * contourCauchyKernelQuadratic data first second target source) 0 := by
  have numerator := (hasDerivAt_const (0 : ℂ) (data.val.2.val.1 source)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const (second.val.2.val.1 source))
  have denominator := (hasDerivAt_const (0 : ℂ) (data.val.1 target - data.val.1 source)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const
      (second.val.1 target - second.val.1 source))
  have first_derivative := (hasDerivAt_const (0 : ℂ) (first.val.2.val.1 source)).div denominator
    (by simpa only [id_eq, zero_mul, add_zero] using separated)
  have second_derivative :=
    (numerator.mul_const (first.val.1 target - first.val.1 source)).div
      (denominator.pow 2)
      (by simpa only [id_eq, zero_mul, add_zero] using pow_ne_zero 2 separated)
  convert first_derivative.sub second_derivative using 1
  simp only [id_eq, zero_mul, add_zero, zero_sub, one_mul, mul_one]
  unfold contourCauchyKernelQuadratic contourCauchyKernelVariation
  generalize difference_eq : data.val.1 target - data.val.1 source = difference at *
  generalize first_eq : first.val.1 target - first.val.1 source = first_increment at *
  generalize second_eq : second.val.1 target - second.val.1 source = second_increment at *
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  field_simp [separated]
  <;> ring

theorem contourCauchyKernelVariation_hasSecondDerivAt_parameter (data direction : PeriodicC1HolderHalf)
    {target source : ℝ} (separated : data.val.1 target - data.val.1 source ≠ 0) :
    HasDerivAt (fun parameter : ℂ =>
      direction.val.2.val.1 source /
          (data.val.1 target - data.val.1 source +
            parameter * (direction.val.1 target - direction.val.1 source)) -
        (data.val.2.val.1 source + parameter * direction.val.2.val.1 source) *
          (direction.val.1 target - direction.val.1 source) /
          (data.val.1 target - data.val.1 source +
            parameter * (direction.val.1 target - direction.val.1 source)) ^ 2)
      (2 * contourCauchyKernelQuadratic data direction direction target source) 0 := by
  have numerator := (hasDerivAt_const (0 : ℂ) (data.val.2.val.1 source)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const (direction.val.2.val.1 source))
  have denominator := (hasDerivAt_const (0 : ℂ) (data.val.1 target - data.val.1 source)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const
      (direction.val.1 target - direction.val.1 source))
  have first := (hasDerivAt_const (0 : ℂ) (direction.val.2.val.1 source)).div denominator
    (by simpa only [id_eq, zero_mul, add_zero] using separated)
  have second := (numerator.mul_const (direction.val.1 target - direction.val.1 source)).div
    (denominator.pow 2) (by simpa only [id_eq, zero_mul, add_zero] using pow_ne_zero 2 separated)
  convert first.sub second using 1
  simp only [id_eq, zero_mul, add_zero, zero_sub, one_mul, mul_one]
  rw [contourCauchyKernelQuadratic_diagonal]
  unfold contourCauchyKernelVariation
  generalize difference_eq : data.val.1 target - data.val.1 source = difference at *
  generalize increment_eq : direction.val.1 target - direction.val.1 source = increment at *
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  field_simp [separated]
  <;> ring

theorem contourCauchyKernelVariation_hasDerivAt_complex_parameter
    (data first second : PeriodicC1HolderHalf) (parameter : ℂ) {target source : ℝ}
    (separated : (data + parameter • second).val.1 target -
      (data + parameter • second).val.1 source ≠ 0) :
    HasDerivAt (fun current : ℂ =>
      contourCauchyKernelVariation (data + current • second) first target source)
      (2 * contourCauchyKernelQuadratic (data + parameter • second) first second target source)
      parameter := by
  have numerator := (hasDerivAt_const parameter (data.val.2.val.1 source)).add
    ((hasDerivAt_id parameter).mul_const (second.val.2.val.1 source))
  have denominator := ((hasDerivAt_const parameter (data.val.1 target)).add
      ((hasDerivAt_id parameter).mul_const (second.val.1 target))).sub
    ((hasDerivAt_const parameter (data.val.1 source)).add
      ((hasDerivAt_id parameter).mul_const (second.val.1 source)))
  have denominator_ne : data.val.1 target + parameter * second.val.1 target -
      (data.val.1 source + parameter * second.val.1 source) ≠ 0 := separated
  have first_derivative := (hasDerivAt_const parameter (first.val.2.val.1 source)).div
    denominator denominator_ne
  have second_derivative :=
    (numerator.mul_const (first.val.1 target - first.val.1 source)).div
      (denominator.pow 2) (pow_ne_zero 2 denominator_ne)
  convert first_derivative.sub second_derivative using 1
  simp only [id_eq, zero_sub, one_mul, mul_one]
  unfold contourCauchyKernelQuadratic contourCauchyKernelVariation
  have value (label : ℝ) : (data + parameter • second).val.1 label =
      data.val.1 label + parameter * second.val.1 label := rfl
  have tangent : (data + parameter • second).val.2.val.1 source =
      data.val.2.val.1 source + parameter * second.val.2.val.1 source := rfl
  rw [value target, value source, tangent]
  simp only [zero_mul, zero_add, zero_sub, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize denominator_eq : data.val.1 target + parameter * second.val.1 target -
      (data.val.1 source + parameter * second.val.1 source) = difference at *
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  field_simp [denominator_ne]
  <;> ring

end

end EulerNonuniqueness.Paper
