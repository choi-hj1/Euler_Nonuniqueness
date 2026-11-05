import EulerNonuniqueness.Section4.ReferenceComputedSaddleBound

noncomputable section

namespace EulerNonuniqueness.Paper

theorem reference_half_decay_exp_bound {frequency : ℝ} (positive : 0 < frequency) :
    Real.exp (-(frequency / 2)) ≤ 3840 / frequency ^ 5 := by
  have power := Real.pow_div_factorial_le_exp (frequency / 2) (by positivity : 0 ≤ frequency / 2) 5
  norm_num only [Nat.factorial] at power
  have multiplied := mul_le_mul_of_nonneg_right power (Real.exp_pos (-(frequency / 2))).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at multiplied
  apply (le_div_iff₀ (pow_pos positive 5)).mpr
  have scaled := mul_le_mul_of_nonneg_left multiplied (by norm_num : (0 : ℝ) ≤ 3840)
  convert scaled using 1 <;> ring

theorem reference_tube_rhs_sharp_bound (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : ℕ) {internal memory bound radius time : ℝ}
    (internalNonnegative : 0 ≤ internal) (boundNonnegative : 0 ≤ bound)
    (radiusNonnegative : 0 ≤ radius) (radiusBound : radius ≤ 1) (timeBound : time ≤ 1) :
    2 * (4 * referenceShapeForcingBudget scales index internal memory bound / scales.omega index +
      radius * Real.exp (-(scales.omega index / 2) * (2 - time))) ≤
    (8 * ((2 * internal * memory ^ 2 + 27648) / Real.pi) +
        8 * ((414720000000 + 3397386240 / Real.pi) * bound / scales.amplitude) + 7680) *
      (scales.strain / scales.omega index + (scales.omega index)⁻¹ ^ 5) := by
  let first := (2 * internal * memory ^ 2 + 27648) / Real.pi
  let second := (414720000000 + 3397386240 / Real.pi) * bound / scales.amplitude
  have firstNonnegative : 0 ≤ first := by dsimp only [first]; positivity
  have secondNonnegative : 0 ≤ second := by dsimp only [second]; positivity
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have exponent : -(scales.omega index / 2) * (2 - time) ≤ -(scales.omega index / 2) := by
    nlinarith only [timeBound, omegaPositive]
  have decay := (Real.exp_le_exp.mpr exponent).trans (reference_half_decay_exp_bound omegaPositive)
  have radiusDecay : radius * Real.exp (-(scales.omega index / 2) * (2 - time)) ≤ 3840 / scales.omega index ^ 5 := by
    exact (mul_le_mul radiusBound decay (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  have estimate := mul_le_mul_of_nonneg_left (add_le_add_left radiusDecay
    (4 * referenceShapeForcingBudget scales index internal memory bound / scales.omega index)) (by norm_num : (0 : ℝ) ≤ 2)
  apply estimate.trans
  calc
    _ = (8 * first) * (scales.strain / scales.omega index) +
        (8 * second + 7680) * ((scales.omega index)⁻¹ ^ 5) := by
      dsimp only [referenceShapeForcingBudget, first, second]
      field_simp [omegaPositive.ne']
      <;> ring
    _ ≤ (8 * first + 8 * second + 7680) * (scales.strain / scales.omega index) +
        (8 * first + 8 * second + 7680) * ((scales.omega index)⁻¹ ^ 5) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (div_nonneg strainNonnegative omegaPositive.le)
        linarith
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = _ := by dsimp only [first, second]; ring

end EulerNonuniqueness.Paper
