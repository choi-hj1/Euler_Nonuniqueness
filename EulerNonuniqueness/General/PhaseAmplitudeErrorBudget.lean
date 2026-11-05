import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem phase_amplitude_error_budget (phase amplitude first second third : ℝ)
    (amplitudeNonnegative : 0 ≤ amplitude) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) (thirdNonnegative : 0 ≤ third) :
    phase * (first + second + third) + amplitude * third * 2 ≤
      (phase + 2 * amplitude + 1) * (first + second + third) := by
  have leftover : 0 ≤ 2 * amplitude * (first + second) + first + second + third := by positivity
  nlinarith only [leftover]

end EulerNonuniqueness.General
