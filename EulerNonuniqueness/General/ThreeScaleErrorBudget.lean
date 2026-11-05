import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem five_term_three_scale_bound (self leading higher tail transport first second third : ℝ)
    (selfNonnegative : 0 ≤ self) (leadingNonnegative : 0 ≤ leading) (higherNonnegative : 0 ≤ higher)
    (tailNonnegative : 0 ≤ tail) (transportNonnegative : 0 ≤ transport)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) (thirdNonnegative : 0 ≤ third) :
    self * third + leading * first + higher * second + tail * second + transport * third ≤
      (self + leading + higher + tail + transport + 1) * (first + second + third) := by
  have leftover : 0 ≤ self * (first + second) + leading * (second + third) +
      higher * (first + third) + tail * (first + third) + transport * (first + second) + first + second + third := by positivity
  nlinarith only [leftover]

end EulerNonuniqueness.General
