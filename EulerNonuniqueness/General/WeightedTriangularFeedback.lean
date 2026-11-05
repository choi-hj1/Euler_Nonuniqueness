import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem weighted_triangular_feedback
    {frequency weight tolerance dilation phase source shear shape forcing : ℝ}
    (frequencyNonnegative : 0 ≤ frequency) (weightPositive : 0 < weight) (toleranceNonnegative : 0 ≤ tolerance)
    (dilationBound : dilation ≤ source / weight)
    (phaseBound : phase ≤ frequency / weight ^ 2 * source + shear / weight)
    (shearBound : shear ≤ tolerance * frequency * (dilation + shape) + forcing) :
    phase ≤ (1 + tolerance) * frequency / weight ^ 2 * source +
      tolerance * frequency / weight * shape + forcing / weight := by
  have first := phaseBound.trans (add_le_add_left (div_le_div_of_nonneg_right shearBound weightPositive.le) _)
  have second := first.trans (add_le_add_left (div_le_div_of_nonneg_right
    (add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add_right dilationBound shape)
      (mul_nonneg toleranceNonnegative frequencyNonnegative)) forcing) weightPositive.le) _)
  apply second.trans_eq
  field_simp
  <;> ring

theorem weighted_integral_three_term_identity
    {first second third : ℝ → ℝ} {terminal weight coefficient : ℝ}
    (terminalNonnegative : 0 ≤ terminal)
    (firstContinuous : ContinuousOn first (Icc 0 terminal))
    (secondContinuous : ContinuousOn second (Icc 0 terminal))
    (thirdContinuous : ContinuousOn third (Icc 0 terminal)) :
    (∫ time in (0 : ℝ)..terminal,
      Real.exp (-weight * time) * (coefficient * (first time + second time) + third time)) =
      coefficient * ((∫ time in (0 : ℝ)..terminal, Real.exp (-weight * time) * first time) +
        ∫ time in (0 : ℝ)..terminal, Real.exp (-weight * time) * second time) +
      ∫ time in (0 : ℝ)..terminal, Real.exp (-weight * time) * third time := by
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have firstIntegrable := (weightContinuous.continuousOn.mul firstContinuous).intervalIntegrable_of_Icc (μ := volume) terminalNonnegative
  have secondIntegrable := (weightContinuous.continuousOn.mul secondContinuous).intervalIntegrable_of_Icc (μ := volume) terminalNonnegative
  have thirdIntegrable := (weightContinuous.continuousOn.mul thirdContinuous).intervalIntegrable_of_Icc (μ := volume) terminalNonnegative
  simp_rw [mul_add, mul_left_comm _ coefficient]
  rw [intervalIntegral.integral_add ((firstIntegrable.const_mul coefficient).add (secondIntegrable.const_mul coefficient)) thirdIntegrable,
    intervalIntegral.integral_add (firstIntegrable.const_mul coefficient) (secondIntegrable.const_mul coefficient),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end EulerNonuniqueness.General
