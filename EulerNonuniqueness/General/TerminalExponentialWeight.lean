import EulerNonuniqueness.General.TwoSidedExponentialKernel

open MeasureTheory Set

namespace EulerNonuniqueness

theorem twoSided_decay_mul_terminal_weight_le
    {decay tailRate base terminal horizon time current : ℝ}
    (tailRateNonnegative : 0 ≤ tailRate) (baseNonnegative : 0 ≤ base)
    (terminalNonnegative : 0 ≤ terminal) :
    Real.exp (-decay * |time - current|) *
        (base + terminal * Real.exp (-tailRate * (horizon - current))) ≤
      Real.exp (-(decay - tailRate) * |time - current|) *
        (base + terminal * Real.exp (-tailRate * (horizon - time))) := by
  have constantBound : Real.exp (-decay * |time - current|) ≤
      Real.exp (-(decay - tailRate) * |time - current|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg (time - current)]
  have terminalBound : Real.exp (-decay * |time - current|) *
      Real.exp (-tailRate * (horizon - current)) ≤
      Real.exp (-(decay - tailRate) * |time - current|) *
        Real.exp (-tailRate * (horizon - time)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have distanceBound : current - time ≤ |time - current| := by
      simpa only [neg_sub] using neg_le_abs (time - current)
    nlinarith
  calc
    _ = base * Real.exp (-decay * |time - current|) +
        terminal * (Real.exp (-decay * |time - current|) * Real.exp (-tailRate * (horizon - current))) := by ring
    _ ≤ base * Real.exp (-(decay - tailRate) * |time - current|) +
        terminal * (Real.exp (-(decay - tailRate) * |time - current|) * Real.exp (-tailRate * (horizon - time))) :=
      add_le_add (mul_le_mul_of_nonneg_left constantBound baseNonnegative)
        (mul_le_mul_of_nonneg_left terminalBound terminalNonnegative)
    _ = _ := by ring

theorem integral_twoSided_terminal_weight_le
    {decay tailRate base terminal horizon time : ℝ}
    (tailRateNonnegative : 0 ≤ tailRate) (ratesOrdered : tailRate < decay)
    (baseNonnegative : 0 ≤ base) (terminalNonnegative : 0 ≤ terminal)
    (inside : time ∈ Icc 0 horizon) :
    (∫ current in (0 : ℝ)..horizon, Real.exp (-decay * |time - current|) *
      (base + terminal * Real.exp (-tailRate * (horizon - current)))) ≤
        (2 / (decay - tailRate)) * (base + terminal * Real.exp (-tailRate * (horizon - time))) := by
  have weightNonnegative : 0 ≤ base + terminal * Real.exp (-tailRate * (horizon - time)) := by positivity
  have integrandContinuous : Continuous (fun current : ℝ => Real.exp (-decay * |time - current|) *
      (base + terminal * Real.exp (-tailRate * (horizon - current)))) := by fun_prop
  have majorantContinuous : Continuous (fun current : ℝ => Real.exp (-(decay - tailRate) * |time - current|) *
      (base + terminal * Real.exp (-tailRate * (horizon - time)))) := by fun_prop
  calc
    _ ≤ ∫ current in (0 : ℝ)..horizon, Real.exp (-(decay - tailRate) * |time - current|) *
        (base + terminal * Real.exp (-tailRate * (horizon - time))) :=
      intervalIntegral.integral_mono_on (inside.1.trans inside.2)
        (integrandContinuous.intervalIntegrable _ _) (majorantContinuous.intervalIntegrable _ _)
        (fun current _ => twoSided_decay_mul_terminal_weight_le tailRateNonnegative baseNonnegative terminalNonnegative)
    _ = (∫ current in (0 : ℝ)..horizon, Real.exp (-(decay - tailRate) * |time - current|)) *
        (base + terminal * Real.exp (-tailRate * (horizon - time))) := intervalIntegral.integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (integral_twoSided_decay_le (sub_pos.mpr ratesOrdered) inside) weightNonnegative

end EulerNonuniqueness
