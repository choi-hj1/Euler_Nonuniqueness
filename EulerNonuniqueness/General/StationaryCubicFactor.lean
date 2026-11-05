import EulerNonuniqueness.General.QuadraticFlatDerivativeBound
import EulerNonuniqueness.General.StationaryPowerFactor

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem exists_stationary_cubic_transverse_factor_of_contDiffAt
    (remainder : Domain → Range) (smooth : ContDiffAt ℝ 3 remainder (0 : Domain))
    (flat : fderiv ℝ remainder (0 : Domain) = 0)
    (secondFlat : fderiv ℝ (fderiv ℝ remainder) (0 : Domain) = 0) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ neutral transverse : Domain,
      ‖neutral‖ + ‖transverse‖ ≤ radius → remainder neutral = 0 →
      ‖remainder (neutral + transverse)‖ ≤
        constant * (‖neutral‖ + ‖transverse‖) ^ 2 * ‖transverse‖ := by
  obtain ⟨radius, positive, constant, nonnegative, actual, estimate⟩ :=
    exists_local_derivative_quadratic_bound_of_contDiffAt_three remainder smooth flat secondFlat
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro neutral transverse inside stationary
  exact stationary_remainder_transverse_power_factor remainder (fderiv ℝ remainder) 2
    nonnegative actual estimate neutral transverse inside stationary

end

end EulerNonuniqueness.General
