import EulerNonuniqueness.Section4.ReferenceRefinedCenterVelocity

noncomputable section

namespace EulerNonuniqueness.Paper

theorem reference_center_defect_scale_bound {frequency length distance hessian memory residual moment : ℝ}
    (frequencyBound : 1 ≤ frequency) (lengthPositive : 0 < length) (distancePositive : 0 < distance)
    (hessianNonnegative : 0 ≤ hessian) (hessianBound : hessian ≤ 1)
    (memoryNonnegative : 0 ≤ memory) (residualNonnegative : 0 ≤ residual)
    (momentBound : moment ≤ memory * hessian * length ^ 2)
    (transportSmall : frequency * length ≤ distance) (lengthSmall : frequency ^ 4 * length ≤ 1) :
    (40000 * frequency * moment + (497664 / Real.pi) * hessian * length ^ 2 +
        residual * (length / frequency ^ 4)) / distance ≤
      (40000 * memory + 497664 / Real.pi + residual) / frequency ^ 4 := by
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyBound
  have powerPositive : 0 < frequency ^ 4 := pow_pos frequencyPositive _
  have lengthDistance : length ≤ distance :=
    (by nlinarith [lengthPositive] : length ≤ frequency * length).trans transportSmall
  have lengthPower : length ≤ 1 / frequency ^ 4 := (le_div_iff₀ powerPositive).mpr (by nlinarith [lengthSmall])
  have momentWeaker : moment ≤ memory * length ^ 2 := by
    apply momentBound.trans
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hessianBound memoryNonnegative) (sq_nonneg length)
  have first : frequency * moment / distance ≤ memory / frequency ^ 4 := by
    have numerator : frequency * moment ≤ memory * length * distance := by
      calc
        _ ≤ frequency * (memory * length ^ 2) := mul_le_mul_of_nonneg_left momentWeaker frequencyPositive.le
        _ = memory * length * (frequency * length) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left transportSmall (mul_nonneg memoryNonnegative lengthPositive.le)
    calc
      _ ≤ memory * length := (div_le_iff₀ distancePositive).mpr numerator
      _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left lengthPower memoryNonnegative
  have second : hessian * length ^ 2 / distance ≤ 1 / frequency ^ 4 := by
    have numerator : hessian * length ^ 2 ≤ length * distance := by
      calc
        _ ≤ 1 * length ^ 2 := mul_le_mul_of_nonneg_right hessianBound (sq_nonneg _)
        _ ≤ _ := by nlinarith [lengthDistance]
    exact ((div_le_iff₀ distancePositive).mpr numerator).trans lengthPower
  have third : (length / frequency ^ 4) / distance ≤ 1 / frequency ^ 4 := by
    apply (div_le_iff₀ distancePositive).mpr
    exact (div_le_div_of_nonneg_right lengthDistance powerPositive.le).trans_eq (by ring)
  have combined := add_le_add (add_le_add (mul_le_mul_of_nonneg_left first (by norm_num : (0 : ℝ) ≤ 40000))
    (mul_le_mul_of_nonneg_left second (by positivity : (0 : ℝ) ≤ 497664 / Real.pi)))
    (mul_le_mul_of_nonneg_left third residualNonnegative)
  convert combined using 1 <;> ring

end EulerNonuniqueness.Paper
