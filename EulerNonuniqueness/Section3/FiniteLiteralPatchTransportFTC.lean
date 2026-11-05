import EulerNonuniqueness.Section3.FiniteLiteralPatchTransportRate

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem integral_fluxTransportRate_eq_sub (flow : FiniteLiteralPatchFlow configuration)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) (short : horizon < flow.duration) (index : Fin count)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ point, HasFDerivAt function (derivative point) point) :
    (∫ time in (0 : ℝ)..horizon, flow.fluxTransportRate index function derivative time) =
      (∫ position in flow.domain horizon index, function (horizon, position)) -
        ∫ position in flow.domain 0 index, function (0, position) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro time member
    rw [uIcc_of_le nonnegative] at member
    apply flow.domain_spacetime_integral_hasDerivAt_flux _ index function derivative
      function_continuous derivative_continuous function_derivative
    exact ⟨by linarith [flow.duration_positive, member.1], member.2.trans_lt short⟩
  · exact (flow.continuous_fluxTransportRate index function derivative function_continuous
      derivative_continuous).intervalIntegrable 0 horizon

theorem integral_actualTransportRate_eq_sub (flow : FiniteLiteralPatchFlow configuration)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) (short : horizon < flow.duration) (index : Fin count)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ point, HasFDerivAt function (derivative point) point) :
    (∫ time in (0 : ℝ)..horizon,
      (∫ position in flow.domain time index, derivative (time, position) (1, 0)) +
        ∫ position in flow.domain time index,
          derivative (time, position) (0, biotSavart (flow.vorticity time) position)) =
      (∫ position in flow.domain horizon index, function (horizon, position)) -
        ∫ position in flow.domain 0 index, function (0, position) := by
  rw [← flow.integral_fluxTransportRate_eq_sub nonnegative short index function derivative
    function_continuous derivative_continuous function_derivative]
  apply intervalIntegral.integral_congr
  intro time member
  rw [uIcc_of_le nonnegative] at member
  exact (flow.fluxTransportRate_eq_actual
    ⟨by linarith [flow.duration_positive, member.1], member.2.trans_lt short⟩
    index function derivative function_continuous derivative_continuous function_derivative).symm

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
