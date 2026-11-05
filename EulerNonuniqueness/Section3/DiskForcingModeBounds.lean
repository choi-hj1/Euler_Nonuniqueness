import EulerNonuniqueness.Section3.DiskForcingModes

namespace EulerNonuniqueness.Paper

noncomputable section

open Set

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeHolderRealSpace

theorem diskCircleMode_tangent (degree : ℕ) (label : ℝ) :
    (diskCircleMode (degree + 1)).val.2.val.1 label =
      (((degree + 1 : ℕ) : ℂ) * Complex.I) * (diskCircleMode (degree + 1)).val.1 label := by
  have original := PeriodicC1HolderHalf.hasDerivAt (diskCircleMode (degree + 1)) label
  have equality : (diskCircleMode (degree + 1)).val.1 =
      fun current => standardCircle current ^ (degree + 1) := funext (diskCircleMode_value _)
  rw [equality] at original
  have identity := original.unique (standardCircle_pow_hasDerivAt degree label)
  simpa only [diskCircleMode_value, mul_assoc] using identity

theorem diskCircleMode_value_norm (degree : ℕ) (label : ℝ) :
    ‖(diskCircleMode degree).val.1 label‖ = 1 := by
  rw [diskCircleMode_value, norm_pow, standardCircle_norm, one_pow]

theorem diskCircleMode_tangent_norm (degree : ℕ) (label : ℝ) :
    ‖(diskCircleMode (degree + 1)).val.2.val.1 label‖ = ((degree + 1 : ℕ) : ℝ) := by
  rw [diskCircleMode_tangent, norm_mul, norm_mul, diskCircleMode_value_norm, Complex.norm_I,
    Complex.norm_natCast, mul_one, mul_one]

theorem diskCircleMode_lipschitz (degree : ℕ) (first second : ℝ) :
    ‖(diskCircleMode (degree + 1)).val.1 first - (diskCircleMode (degree + 1)).val.1 second‖ ≤
      ((degree + 1 : ℕ) : ℝ) * |first - second| := by
  have actual := (convex_uIcc second first).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun current _ => (PeriodicC1HolderHalf.hasDerivAt (diskCircleMode (degree + 1)) current).hasDerivWithinAt)
    (fun current _ => (diskCircleMode_tangent_norm degree current).le) left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using actual

theorem diskCircleMode_tangent_holder (degree : ℕ) (first second : ℝ) :
    ‖(diskCircleMode (degree + 1)).val.2.val.1 first - (diskCircleMode (degree + 1)).val.2.val.1 second‖ ≤
      2 * (((degree + 1 : ℕ) : ℝ) ^ 2) * Real.sqrt |first - second| := by
  let speed : ℝ := ((degree + 1 : ℕ) : ℝ)
  have speedLarge : 1 ≤ speed := by dsimp only [speed]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le degree)
  have speedNonnegative : 0 ≤ speed := zero_le_one.trans speedLarge
  have linear : ‖(diskCircleMode (degree + 1)).val.2.val.1 first -
      (diskCircleMode (degree + 1)).val.2.val.1 second‖ ≤ speed ^ 2 * |first - second| := by
    rw [diskCircleMode_tangent, diskCircleMode_tangent, ← mul_sub, norm_mul, norm_mul,
      Complex.norm_I, Complex.norm_natCast, mul_one]
    have actual := mul_le_mul_of_nonneg_left (diskCircleMode_lipschitz degree first second) speedNonnegative
    simpa only [speed, pow_two, mul_assoc] using actual
  have bounded : ‖(diskCircleMode (degree + 1)).val.2.val.1 first -
      (diskCircleMode (degree + 1)).val.2.val.1 second‖ ≤ 2 * speed := by
    apply (norm_sub_le _ _).trans
    rw [diskCircleMode_tangent_norm, diskCircleMode_tangent_norm]
    change speed + speed ≤ 2 * speed
    linarith
  by_cases small : |first - second| ≤ 1
  · have distanceBound : |first - second| ≤ Real.sqrt |first - second| :=
      Real.le_sqrt_of_sq_le (by nlinarith [abs_nonneg (first - second)])
    apply linear.trans
    calc
      speed ^ 2 * |first - second| ≤ speed ^ 2 * Real.sqrt |first - second| :=
        mul_le_mul_of_nonneg_left distanceBound (sq_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg speed) (Real.sqrt_nonneg |first - second|)]
  · have rootLarge : 1 ≤ Real.sqrt |first - second| := Real.le_sqrt_of_sq_le (by linarith)
    apply bounded.trans
    have squareLarge : speed ≤ speed ^ 2 := by nlinarith
    calc
      2 * speed ≤ 2 * speed ^ 2 := by linarith
      _ ≤ _ := by
        have actual := mul_le_mul_of_nonneg_left rootLarge (show 0 ≤ 2 * speed ^ 2 by positivity)
        simpa only [mul_one] using actual

theorem diskCircleMode_norm_bound (degree : ℕ) :
    ‖diskCircleMode (degree + 1)‖ ≤ 2 * (((degree + 1 : ℕ) : ℝ) ^ 2) := by
  let data := diskCircleMode (degree + 1)
  have reconstructed : PeriodicC1HolderHalf.ofFunctions data.val.1 data.val.2.val.1
      data.val.1.continuous data.val.2.val.1.continuous 1 ((degree + 1 : ℕ) : ℝ)
      (2 * (((degree + 1 : ℕ) : ℝ) ^ 2))
      (fun label => (diskCircleMode_value_norm _ label).le)
      (fun label => (diskCircleMode_tangent_norm degree label).le)
      (diskCircleMode_tangent_holder degree) (PeriodicC1HolderHalf.hasDerivAt data)
      (PeriodicC1HolderHalf.periodic data) (PeriodicHolderHalf.periodic data.val.2) = data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl
  have bound := PeriodicC1HolderHalf.ofFunctions_norm_bound data.val.1 data.val.2.val.1
    data.val.1.continuous data.val.2.val.1.continuous (by norm_num : (0 : ℝ) ≤ 1)
    (by positivity : (0 : ℝ) ≤ ((degree + 1 : ℕ) : ℝ)) (by positivity : (0 : ℝ) ≤ 2 * (((degree + 1 : ℕ) : ℝ) ^ 2))
    (fun label => (diskCircleMode_value_norm _ label).le)
    (fun label => (diskCircleMode_tangent_norm degree label).le)
    (diskCircleMode_tangent_holder degree) (PeriodicC1HolderHalf.hasDerivAt data)
    (PeriodicC1HolderHalf.periodic data) (PeriodicHolderHalf.periodic data.val.2)
  rw [reconstructed] at bound
  apply bound.trans
  have speedLarge : (1 : ℝ) ≤ ((degree + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le degree)
  apply max_le
  · nlinarith
  · apply max_le
    · nlinarith
    · exact le_rfl

end

end EulerNonuniqueness.Paper
