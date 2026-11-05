import EulerNonuniqueness.General.TerminalExponentialWeight

open MeasureTheory Set

namespace EulerNonuniqueness

theorem twoSided_terminal_tube_bound
    {trajectory : ℝ → ℝ} {decay tailRate base terminal horizon initial feedback : ℝ}
    (horizonNonnegative : 0 ≤ horizon)
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (trajectoryNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ trajectory time)
    (tailRateNonnegative : 0 ≤ tailRate) (ratesOrdered : tailRate < decay)
    (baseNonnegative : 0 ≤ base) (terminalNonnegative : 0 ≤ terminal)
    (weightNontrivial : 0 < base + terminal)
    (feedbackNonnegative : 0 ≤ feedback)
    (small : feedback * (2 / (decay - tailRate)) < 1)
    (inequality : ∀ time ∈ Icc 0 horizon,
      trajectory time ≤ initial * (base + terminal * Real.exp (-tailRate * (horizon - time))) +
        feedback * ∫ current in (0 : ℝ)..horizon,
          Real.exp (-decay * |time - current|) * trajectory current) :
    ∀ time ∈ Icc 0 horizon, trajectory time ≤
      initial / (1 - feedback * (2 / (decay - tailRate))) *
        (base + terminal * Real.exp (-tailRate * (horizon - time))) := by
  have weightPositive (time : ℝ) : 0 < base + terminal * Real.exp (-tailRate * (horizon - time)) := by
    by_cases basePositive : 0 < base
    · positivity
    · have terminalPositive : 0 < terminal := by linarith
      positivity
  apply weighted_integral_absorption_on_Icc
    (weight := fun time => base + terminal * Real.exp (-tailRate * (horizon - time)))
    (kernel := fun time current => Real.exp (-decay * |time - current|))
    horizonNonnegative trajectoryContinuous
    (by fun_prop) trajectoryNonnegative (fun time _ => weightPositive time)
    (fun time _ => by fun_prop) (fun time _ current _ => (Real.exp_pos _).le)
    feedbackNonnegative small
    (fun time inside => integral_twoSided_terminal_weight_le tailRateNonnegative ratesOrdered
      baseNonnegative terminalNonnegative inside) inequality

end EulerNonuniqueness
