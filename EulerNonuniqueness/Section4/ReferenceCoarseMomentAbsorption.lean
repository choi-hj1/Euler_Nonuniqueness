import EulerNonuniqueness.Section4.ReferenceCenterDefectScale

noncomputable section

namespace EulerNonuniqueness.Paper

theorem coarse_moment_le_length_sq {constant strain hessian length time moment : ℝ}
    (constantNonnegative : 0 ≤ constant) (strainNonnegative : 0 ≤ strain)
    (hessianNonnegative : 0 ≤ hessian) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ 2)
    (strainSmall : constant * strain ≤ 1)
    (hessianSmall : 2 * constant * Real.exp 2 * hessian ≤ 1)
    (bound : moment ≤ constant * hessian * length ^ 2 * time * Real.exp (constant * strain * time)) :
    moment ≤ length ^ 2 := by
  have exponentBound : constant * strain * time ≤ 2 := by
    have scaled := mul_le_mul_of_nonneg_right strainSmall timeNonnegative
    nlinarith only [scaled, timeBound]
  have exponentialBound := Real.exp_le_exp.mpr exponentBound
  calc
    moment ≤ constant * hessian * length ^ 2 * time * Real.exp (constant * strain * time) := bound
    _ ≤ constant * hessian * length ^ 2 * 2 * Real.exp 2 := by
      gcongr
    _ = (2 * constant * Real.exp 2 * hessian) * length ^ 2 := by ring
    _ ≤ length ^ 2 := by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hessianSmall (sq_nonneg length)

theorem reference_center_defect_absorbed_scale_bound
    {frequency length distance hessian residual moment : ℝ}
    (frequencyBound : 1 ≤ frequency) (lengthPositive : 0 < length) (distancePositive : 0 < distance)
    (hessianBound : hessian ≤ 1) (residualBound : residual ≤ frequency)
    (momentBound : moment ≤ length ^ 2)
    (transportSmall : frequency * length ≤ distance) (lengthSmall : frequency ^ 4 * length ≤ 1) :
    (40000 * frequency * moment + (497664 / Real.pi) * hessian * length ^ 2 +
        residual * (length / frequency ^ 4)) / distance ≤
      (40001 + 497664 / Real.pi) / frequency ^ 4 := by
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyBound
  have powerPositive : 0 < frequency ^ 4 := pow_pos frequencyPositive _
  have core := reference_center_defect_scale_bound frequencyBound lengthPositive distancePositive
    (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 1 by norm_num)
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 0 by norm_num)
    (by simpa only [one_mul] using momentBound) transportSmall lengthSmall
  simp only [one_mul, mul_one, zero_mul, add_zero] at core
  have weakened : (40000 * frequency * moment + (497664 / Real.pi) * hessian * length ^ 2) / distance ≤
      (40000 * frequency * moment + (497664 / Real.pi) * length ^ 2) / distance := by
    apply div_le_div_of_nonneg_right _ distancePositive.le
    simpa only [mul_one] using
      (add_le_add_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hessianBound (by positivity : (0 : ℝ) ≤ 497664 / Real.pi))
        (sq_nonneg length)) (40000 * frequency * moment))
  have tail : residual * (length / frequency ^ 4) / distance ≤ 1 / frequency ^ 4 := by
    apply (div_le_iff₀ distancePositive).mpr
    have numerator : residual * length ≤ distance :=
      (mul_le_mul_of_nonneg_right residualBound lengthPositive.le).trans transportSmall
    calc
      residual * (length / frequency ^ 4) = residual * length / frequency ^ 4 := by ring
      _ ≤ distance / frequency ^ 4 := div_le_div_of_nonneg_right numerator powerPositive.le
      _ = (1 / frequency ^ 4) * distance := by ring
  calc
    _ = (40000 * frequency * moment + (497664 / Real.pi) * hessian * length ^ 2) / distance +
        residual * (length / frequency ^ 4) / distance := by ring
    _ ≤ (40000 + 497664 / Real.pi) / frequency ^ 4 + 1 / frequency ^ 4 :=
      add_le_add (weakened.trans core) tail
    _ = _ := by ring

end EulerNonuniqueness.Paper
