import EulerNonuniqueness.General.TerminalExponentialWeight

open MeasureTheory Set

namespace EulerNonuniqueness

noncomputable section

def ratePrimitive (rate : ℝ → ℝ) (time : ℝ) : ℝ := ∫ current in (0 : ℝ)..time, rate current

theorem ratePrimitive_hasDerivAt {rate : ℝ → ℝ} (rateContinuous : Continuous rate) (time : ℝ) :
    HasDerivAt (ratePrimitive rate) (rate time) time :=
  (rateContinuous.integral_hasStrictDerivAt 0 time).hasDerivAt

theorem ratePrimitive_continuous {rate : ℝ → ℝ} (rateContinuous : Continuous rate) :
    Continuous (ratePrimitive rate) :=
  continuous_iff_continuousAt.mpr (fun time => (ratePrimitive_hasDerivAt rateContinuous time).continuousAt)

theorem variable_integrating_factor_hasDerivAt
    {rate trajectory forcing : ℝ → ℝ} {time : ℝ}
    (rateContinuous : Continuous rate)
    (equation : HasDerivAt trajectory (rate time * trajectory time + forcing time) time) :
    HasDerivAt (fun current => Real.exp (-ratePrimitive rate current) * trajectory current)
      (Real.exp (-ratePrimitive rate time) * forcing time) time := by
  convert ((ratePrimitive_hasDerivAt rateContinuous time).neg.exp).mul equation using 1
  ring

theorem variable_integrating_factor_integral
    {rate trajectory forcing : ℝ → ℝ} {first last : ℝ}
    (rateContinuous : Continuous rate)
    (forcingContinuous : ContinuousOn forcing (uIcc first last))
    (equation : ∀ time ∈ uIcc first last,
      HasDerivAt trajectory (rate time * trajectory time + forcing time) time) :
    (∫ time in first..last, Real.exp (-ratePrimitive rate time) * forcing time) =
      Real.exp (-ratePrimitive rate last) * trajectory last -
        Real.exp (-ratePrimitive rate first) * trajectory first := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time inside => variable_integrating_factor_hasDerivAt rateContinuous (equation time inside))
    (((ratePrimitive_continuous rateContinuous).neg.rexp.continuousOn.mul forcingContinuous).intervalIntegrable)

theorem scalar_variable_duhamel
    {rate trajectory forcing : ℝ → ℝ} {first last : ℝ}
    (rateContinuous : Continuous rate)
    (forcingContinuous : ContinuousOn forcing (uIcc first last))
    (equation : ∀ time ∈ uIcc first last,
      HasDerivAt trajectory (rate time * trajectory time + forcing time) time) :
    trajectory last = Real.exp (ratePrimitive rate last - ratePrimitive rate first) * trajectory first +
      ∫ time in first..last, Real.exp (ratePrimitive rate last - ratePrimitive rate time) * forcing time := by
  have identity := variable_integrating_factor_integral rateContinuous forcingContinuous equation
  have cancellation : Real.exp (ratePrimitive rate last) * Real.exp (-ratePrimitive rate last) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have multiplied := congrArg (fun value => Real.exp (ratePrimitive rate last) * value) identity
  dsimp only at multiplied
  rw [mul_sub, ← mul_assoc, cancellation, one_mul] at multiplied
  have combined (time : ℝ) : Real.exp (ratePrimitive rate last) * Real.exp (-ratePrimitive rate time) =
      Real.exp (ratePrimitive rate last - ratePrimitive rate time) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  rw [← mul_assoc, combined first] at multiplied
  have integralIdentity : Real.exp (ratePrimitive rate last) *
      (∫ time in first..last, Real.exp (-ratePrimitive rate time) * forcing time) =
      ∫ time in first..last, Real.exp (ratePrimitive rate last - ratePrimitive rate time) * forcing time := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    dsimp only
    rw [← mul_assoc, combined time]
  rw [integralIdentity] at multiplied
  linarith

end

end EulerNonuniqueness
