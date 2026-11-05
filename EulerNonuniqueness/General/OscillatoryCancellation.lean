import Mathlib

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem norm_exp_negative_two_mul_I (phase : ℝ) :
    ‖Complex.exp (-2 * Complex.I * (phase : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem oscillatory_cancellation_identity
    {amplitude amplitudeDerivative : ℝ → ℂ}
    {dilation dilationDerivative phase phaseError : ℝ → ℝ}
    {frequency terminal : ℝ} (frequencyNonzero : frequency ≠ 0)
    (amplitudeEquation : ∀ time ∈ uIcc 0 terminal,
      HasDerivAt amplitude (amplitudeDerivative time) time)
    (dilationEquation : ∀ time ∈ uIcc 0 terminal,
      HasDerivAt dilation (dilationDerivative time) time)
    (phaseEquation : ∀ time ∈ uIcc 0 terminal,
      HasDerivAt phase (-frequency / dilation time + phaseError time) time)
    (dilationNonzero : ∀ time ∈ uIcc 0 terminal, dilation time ≠ 0)
    (amplitudeDerivativeContinuous : ContinuousOn amplitudeDerivative (uIcc 0 terminal))
    (dilationDerivativeContinuous : ContinuousOn dilationDerivative (uIcc 0 terminal))
    (phaseErrorContinuous : ContinuousOn phaseError (uIcc 0 terminal)) :
    (∫ time in (0 : ℝ)..terminal,
      amplitude time * Complex.exp (-2 * Complex.I * (phase time : ℂ))) =
      (dilation terminal : ℂ) * amplitude terminal *
          Complex.exp (-2 * Complex.I * (phase terminal : ℂ)) / (2 * Complex.I * (frequency : ℂ)) -
        (dilation 0 : ℂ) * amplitude 0 *
          Complex.exp (-2 * Complex.I * (phase 0 : ℂ)) / (2 * Complex.I * (frequency : ℂ)) -
      (∫ time in (0 : ℝ)..terminal,
        ((dilation time : ℂ) * amplitudeDerivative time +
          (dilationDerivative time : ℂ) * amplitude time) *
          Complex.exp (-2 * Complex.I * (phase time : ℂ)) / (2 * Complex.I * (frequency : ℂ))) +
      ∫ time in (0 : ℝ)..terminal,
        (dilation time : ℂ) * amplitude time * (phaseError time : ℂ) *
          Complex.exp (-2 * Complex.I * (phase time : ℂ)) / (frequency : ℂ) := by
  let oscillation := fun time => Complex.exp (-2 * Complex.I * (phase time : ℂ))
  let mainTerm := fun time => amplitude time * oscillation time
  let differentiatedTerm := fun time =>
    ((dilation time : ℂ) * amplitudeDerivative time +
      (dilationDerivative time : ℂ) * amplitude time) * oscillation time /
      (2 * Complex.I * (frequency : ℂ))
  let errorTerm := fun time =>
    (dilation time : ℂ) * amplitude time * (phaseError time : ℂ) *
      oscillation time / (frequency : ℂ)
  let primitive := fun time =>
    (dilation time : ℂ) * amplitude time * oscillation time / (2 * Complex.I * (frequency : ℂ))
  have amplitudeContinuous : ContinuousOn amplitude (uIcc 0 terminal) :=
    fun time inside => (amplitudeEquation time inside).continuousAt.continuousWithinAt
  have dilationContinuous : ContinuousOn dilation (uIcc 0 terminal) :=
    fun time inside => (dilationEquation time inside).continuousAt.continuousWithinAt
  have phaseContinuous : ContinuousOn phase (uIcc 0 terminal) :=
    fun time inside => (phaseEquation time inside).continuousAt.continuousWithinAt
  have dilationComplexContinuous := Complex.continuous_ofReal.comp_continuousOn dilationContinuous
  have dilationDerivativeComplexContinuous := Complex.continuous_ofReal.comp_continuousOn dilationDerivativeContinuous
  have phaseComplexContinuous := Complex.continuous_ofReal.comp_continuousOn phaseContinuous
  have phaseErrorComplexContinuous := Complex.continuous_ofReal.comp_continuousOn phaseErrorContinuous
  have oscillationContinuous : ContinuousOn oscillation (uIcc 0 terminal) := by
    exact Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul phaseComplexContinuous)
  have mainIntegrable : IntervalIntegrable mainTerm volume 0 terminal :=
    (amplitudeContinuous.mul oscillationContinuous).intervalIntegrable
  have differentiatedIntegrable : IntervalIntegrable differentiatedTerm volume 0 terminal := by
    exact (((dilationComplexContinuous.mul amplitudeDerivativeContinuous).add
      (dilationDerivativeComplexContinuous.mul amplitudeContinuous)).mul oscillationContinuous).div_const _ |>.intervalIntegrable
  have errorIntegrable : IntervalIntegrable errorTerm volume 0 terminal := by
    exact (((dilationComplexContinuous.mul amplitudeContinuous).mul phaseErrorComplexContinuous).mul
      oscillationContinuous).div_const _ |>.intervalIntegrable
  have primitiveDerivative (time : ℝ) (inside : time ∈ uIcc 0 terminal) :
      HasDerivAt primitive (mainTerm time + differentiatedTerm time - errorTerm time) time := by
    have exponentialDerivative :=
      (((phaseEquation time inside).ofReal_comp.const_mul (-2 * Complex.I)).cexp)
    have derivative := ((((dilationEquation time inside).ofReal_comp.mul
      (amplitudeEquation time inside)).mul exponentialDerivative).div_const (2 * Complex.I * (frequency : ℂ)))
    convert derivative using 1
    dsimp only [primitive, mainTerm, differentiatedTerm, errorTerm, oscillation]
    push_cast
    have frequencyComplexNonzero : (frequency : ℂ) ≠ 0 := by exact_mod_cast frequencyNonzero
    have dilationComplexNonzero : (dilation time : ℂ) ≠ 0 := by exact_mod_cast dilationNonzero time inside
    field_simp
    ring
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt primitiveDerivative
    ((mainIntegrable.add differentiatedIntegrable).sub errorIntegrable)
  rw [intervalIntegral.integral_sub (mainIntegrable.add differentiatedIntegrable) errorIntegrable,
    intervalIntegral.integral_add mainIntegrable differentiatedIntegrable] at identity
  change (∫ time in (0 : ℝ)..terminal, mainTerm time) =
    primitive terminal - primitive 0 - (∫ time in (0 : ℝ)..terminal, differentiatedTerm time) +
      ∫ time in (0 : ℝ)..terminal, errorTerm time
  linear_combination identity

end EulerNonuniqueness
