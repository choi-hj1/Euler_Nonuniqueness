import EulerNonuniqueness.Section3.ContourKernelParameter
import Mathlib.Analysis.Calculus.Deriv.Slope

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def contourCauchyKernelVariation (data direction : PeriodicC1HolderHalf) (target source : ℝ) : ℂ :=
  direction.val.2.val.1 source / (data.val.1 target - data.val.1 source) -
    data.val.2.val.1 source * (direction.val.1 target - direction.val.1 source) /
      (data.val.1 target - data.val.1 source) ^ 2

theorem contourCauchyKernelVariation_hasDerivAt_parameter (data direction : PeriodicC1HolderHalf)
    {target source : ℝ} (separated : data.val.1 target - data.val.1 source ≠ 0) :
    HasDerivAt (fun parameter : ℂ =>
      (data.val.2.val.1 source + parameter * direction.val.2.val.1 source) /
        (data.val.1 target - data.val.1 source + parameter * (direction.val.1 target - direction.val.1 source)))
      (contourCauchyKernelVariation data direction target source) 0 := by
  have numerator := (hasDerivAt_const (0 : ℂ) (data.val.2.val.1 source)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const (direction.val.2.val.1 source))
  have denominator := (hasDerivAt_const (0 : ℂ) (data.val.1 target - data.val.1 source)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const (direction.val.1 target - direction.val.1 source))
  have result := numerator.div denominator (by simpa using separated)
  convert result using 1
  simp only [zero_add, zero_mul, add_zero, one_mul]
  unfold contourCauchyKernelVariation
  field_simp
  ring

theorem contourCauchyKernelVariation_primitive_hasDerivAt (data direction : PeriodicC1HolderHalf)
    {target source : ℝ} (separated : data.val.1 target - data.val.1 source ≠ 0) :
    HasDerivAt (fun parameter => (direction.val.1 parameter - direction.val.1 target) /
      (data.val.1 target - data.val.1 parameter)) (contourCauchyKernelVariation data direction target source) source := by
  have result := ((PeriodicC1HolderHalf.hasDerivAt direction source).sub_const (direction.val.1 target)).div
    ((hasDerivAt_const source (data.val.1 target)).sub (PeriodicC1HolderHalf.hasDerivAt data source)) separated
  convert result using 1
  simp only [zero_sub]
  unfold contourCauchyKernelVariation
  field_simp
  ring

theorem contourCauchyKernelVariation_weak_bound (data direction : PeriodicC1HolderHalf)
    {target source chord : ℝ} (distinct : source ≠ target) (chord_positive : 0 < chord)
    (lower : chord * |target - source| ≤ ‖data.val.1 target - data.val.1 source‖) :
    ‖contourCauchyKernelVariation data direction target source‖ ≤
      2 * ‖data‖ * ‖direction‖ / (chord ^ 2 * Real.sqrt |target - source|) := by
  let distance := |target - source|
  have distance_positive : 0 < distance := abs_pos.mpr (sub_ne_zero.mpr distinct.symm)
  have root_positive : 0 < Real.sqrt distance := Real.sqrt_pos.mpr distance_positive
  have root_square := Real.sq_sqrt distance_positive.le
  have denominator_positive : 0 < ‖data.val.1 target - data.val.1 source‖ :=
    (mul_pos chord_positive distance_positive).trans_le lower
  have denominator_ne := norm_ne_zero_iff.mp denominator_positive.ne'
  have remainder (function : PeriodicC1HolderHalf) :
      ‖function.val.1 target - function.val.1 source - (target - source) • function.val.2.val.1 source‖ ≤
        ‖function‖ * Real.sqrt distance * distance := by
    have result := contour_taylor_remainder_unordered (source := target) (target := source) (norm_nonneg function)
      (fun parameter _ => PeriodicC1HolderHalf.hasDerivAt function parameter)
      (fun parameter _ => PeriodicC1HolderHalf.derivative_holder_bound function parameter source)
    convert result using 1
    · rw [← norm_neg]
      congr 1
      simp only [Complex.real_smul]
      push_cast
      ring
    · simp only [distance, abs_sub_comm source target]
  let numerator := direction.val.2.val.1 source * (data.val.1 target - data.val.1 source) -
    data.val.2.val.1 source * (direction.val.1 target - direction.val.1 source)
  have numerator_identity : numerator =
      direction.val.2.val.1 source * (data.val.1 target - data.val.1 source -
        (target - source) • data.val.2.val.1 source) -
      data.val.2.val.1 source * (direction.val.1 target - direction.val.1 source -
        (target - source) • direction.val.2.val.1 source) := by
    dsimp only [numerator]
    simp only [Complex.real_smul]
    ring
  have numerator_bound : ‖numerator‖ ≤ 2 * ‖data‖ * ‖direction‖ * Real.sqrt distance * distance := by
    rw [numerator_identity]
    apply (norm_sub_le _ _).trans
    simp only [norm_mul]
    have first := mul_le_mul (PeriodicC1HolderHalf.speed_bound direction source) (remainder data)
      (norm_nonneg _) (norm_nonneg direction)
    have second := mul_le_mul (PeriodicC1HolderHalf.speed_bound data source) (remainder direction)
      (norm_nonneg _) (norm_nonneg data)
    nlinarith
  have identity : contourCauchyKernelVariation data direction target source =
      numerator / (data.val.1 target - data.val.1 source) ^ 2 := by
    unfold contourCauchyKernelVariation numerator
    field_simp
    ring
  rw [identity, norm_div, norm_pow]
  calc
    _ ≤ (2 * ‖data‖ * ‖direction‖ * Real.sqrt distance * distance) /
        ‖data.val.1 target - data.val.1 source‖ ^ 2 :=
      div_le_div_of_nonneg_right numerator_bound (sq_nonneg _)
    _ ≤ (2 * ‖data‖ * ‖direction‖ * Real.sqrt distance * distance) / (chord * distance) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        ((sq_le_sq₀ (mul_nonneg chord_positive.le distance_positive.le) (norm_nonneg _)).mpr lower)
    _ = _ := by
      change _ = 2 * ‖data‖ * ‖direction‖ / (chord ^ 2 * Real.sqrt distance)
      field_simp [chord_positive.ne', distance_positive.ne', root_positive.ne']
      ring_nf
      rw [root_square]
      ring

end

end EulerNonuniqueness.Paper
