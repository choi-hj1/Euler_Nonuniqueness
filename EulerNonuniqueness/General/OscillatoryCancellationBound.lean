import EulerNonuniqueness.General.OscillatoryCancellation

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem oscillatory_cancellation_norm_le
    {amplitude amplitudeDerivative : ℝ → ℂ}
    {dilation dilationDerivative phase phaseError : ℝ → ℝ}
    {frequency terminal dilationBound amplitudeBound amplitudeDerivativeBound
      dilationDerivativeBound phaseErrorBound : ℝ}
    (frequencyPositive : 0 < frequency) (terminalNonnegative : 0 ≤ terminal)
    (amplitudeEquation : ∀ time ∈ Icc 0 terminal,
      HasDerivAt amplitude (amplitudeDerivative time) time)
    (dilationEquation : ∀ time ∈ Icc 0 terminal,
      HasDerivAt dilation (dilationDerivative time) time)
    (phaseEquation : ∀ time ∈ Icc 0 terminal,
      HasDerivAt phase (-frequency / dilation time + phaseError time) time)
    (dilationNonzero : ∀ time ∈ Icc 0 terminal, dilation time ≠ 0)
    (amplitudeDerivativeContinuous : ContinuousOn amplitudeDerivative (Icc 0 terminal))
    (dilationDerivativeContinuous : ContinuousOn dilationDerivative (Icc 0 terminal))
    (phaseErrorContinuous : ContinuousOn phaseError (Icc 0 terminal))
    (dilationControl : ∀ time ∈ Icc 0 terminal, |dilation time| ≤ dilationBound)
    (amplitudeControl : ∀ time ∈ Icc 0 terminal, ‖amplitude time‖ ≤ amplitudeBound)
    (amplitudeDerivativeControl : ∀ time ∈ Icc 0 terminal, ‖amplitudeDerivative time‖ ≤ amplitudeDerivativeBound)
    (dilationDerivativeControl : ∀ time ∈ Icc 0 terminal, |dilationDerivative time| ≤ dilationDerivativeBound)
    (phaseErrorControl : ∀ time ∈ Icc 0 terminal, |phaseError time| ≤ phaseErrorBound) :
    ‖∫ time in (0 : ℝ)..terminal,
      amplitude time * Complex.exp (-2 * Complex.I * (phase time : ℂ))‖ ≤
      (2 * dilationBound * amplitudeBound + terminal *
        (dilationBound * amplitudeDerivativeBound + dilationDerivativeBound * amplitudeBound +
          2 * dilationBound * amplitudeBound * phaseErrorBound)) / (2 * frequency) := by
  have initialInside : (0 : ℝ) ∈ Icc 0 terminal := ⟨le_rfl, terminalNonnegative⟩
  have dilationBoundNonnegative := (abs_nonneg (dilation 0)).trans (dilationControl 0 initialInside)
  have amplitudeBoundNonnegative := (norm_nonneg (amplitude 0)).trans (amplitudeControl 0 initialInside)
  have amplitudeDerivativeBoundNonnegative :=
    (norm_nonneg (amplitudeDerivative 0)).trans (amplitudeDerivativeControl 0 initialInside)
  have dilationDerivativeBoundNonnegative :=
    (abs_nonneg (dilationDerivative 0)).trans (dilationDerivativeControl 0 initialInside)
  have phaseErrorBoundNonnegative := (abs_nonneg (phaseError 0)).trans (phaseErrorControl 0 initialInside)
  let oscillation := fun time => Complex.exp (-2 * Complex.I * (phase time : ℂ))
  let primitive := fun time => (dilation time : ℂ) * amplitude time * oscillation time /
    (2 * Complex.I * (frequency : ℂ))
  let differentiatedTerm := fun time =>
    ((dilation time : ℂ) * amplitudeDerivative time +
      (dilationDerivative time : ℂ) * amplitude time) * oscillation time /
      (2 * Complex.I * (frequency : ℂ))
  let errorTerm := fun time =>
    (dilation time : ℂ) * amplitude time * (phaseError time : ℂ) * oscillation time / (frequency : ℂ)
  have denominatorNorm : ‖(2 : ℂ) * Complex.I * (frequency : ℂ)‖ = 2 * frequency := by
    simp [norm_mul, abs_of_pos frequencyPositive]
  have frequencyNorm : ‖(frequency : ℂ)‖ = frequency := by
    simp [abs_of_pos frequencyPositive]
  have primitiveBound (time : ℝ) (inside : time ∈ Icc 0 terminal) :
      ‖primitive time‖ ≤ dilationBound * amplitudeBound / (2 * frequency) := by
    dsimp only [primitive, oscillation]
    rw [norm_div, norm_mul, norm_mul, norm_exp_negative_two_mul_I, mul_one, denominatorNorm,
      Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (dilationControl time inside) (amplitudeControl time inside)
        (norm_nonneg _) dilationBoundNonnegative) (by positivity)
  have differentiatedBound (time : ℝ) (inside : time ∈ Icc 0 terminal) :
      ‖differentiatedTerm time‖ ≤
        (dilationBound * amplitudeDerivativeBound + dilationDerivativeBound * amplitudeBound) / (2 * frequency) := by
    dsimp only [differentiatedTerm, oscillation]
    rw [norm_div, norm_mul, norm_exp_negative_two_mul_I, mul_one, denominatorNorm]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact add_le_add
      (mul_le_mul (dilationControl time inside) (amplitudeDerivativeControl time inside)
        (norm_nonneg _) dilationBoundNonnegative)
      (mul_le_mul (dilationDerivativeControl time inside) (amplitudeControl time inside)
        (norm_nonneg _) dilationDerivativeBoundNonnegative)
  have errorBound (time : ℝ) (inside : time ∈ Icc 0 terminal) :
      ‖errorTerm time‖ ≤ dilationBound * amplitudeBound * phaseErrorBound / frequency := by
    dsimp only [errorTerm, oscillation]
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_exp_negative_two_mul_I, mul_one, frequencyNorm,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    apply div_le_div_of_nonneg_right _ frequencyPositive.le
    exact mul_le_mul
      (mul_le_mul (dilationControl time inside) (amplitudeControl time inside)
        (norm_nonneg _) dilationBoundNonnegative)
      (phaseErrorControl time inside) (abs_nonneg _) (mul_nonneg dilationBoundNonnegative amplitudeBoundNonnegative)
  have identity := oscillatory_cancellation_identity (amplitude := amplitude)
    (amplitudeDerivative := amplitudeDerivative) (dilation := dilation)
    (dilationDerivative := dilationDerivative) (phase := phase) (phaseError := phaseError)
    (terminal := terminal) frequencyPositive.ne'
    (by simpa only [uIcc_of_le terminalNonnegative] using amplitudeEquation)
    (by simpa only [uIcc_of_le terminalNonnegative] using dilationEquation)
    (by simpa only [uIcc_of_le terminalNonnegative] using phaseEquation)
    (by simpa only [uIcc_of_le terminalNonnegative] using dilationNonzero)
    (by simpa only [uIcc_of_le terminalNonnegative] using amplitudeDerivativeContinuous)
    (by simpa only [uIcc_of_le terminalNonnegative] using dilationDerivativeContinuous)
    (by simpa only [uIcc_of_le terminalNonnegative] using phaseErrorContinuous)
  change (∫ time in (0 : ℝ)..terminal, amplitude time * oscillation time) =
    primitive terminal - primitive 0 - (∫ time in (0 : ℝ)..terminal, differentiatedTerm time) +
      ∫ time in (0 : ℝ)..terminal, errorTerm time at identity
  rw [identity]
  have differentiatedIntegralBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun time (inside : time ∈ uIoc 0 terminal) =>
      differentiatedBound time (by rw [uIoc_of_le terminalNonnegative] at inside; exact ⟨inside.1.le, inside.2⟩))
  have errorIntegralBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun time (inside : time ∈ uIoc 0 terminal) =>
      errorBound time (by rw [uIoc_of_le terminalNonnegative] at inside; exact ⟨inside.1.le, inside.2⟩))
  rw [sub_zero, abs_of_nonneg terminalNonnegative] at differentiatedIntegralBound errorIntegralBound
  calc
    _ ≤ ‖primitive terminal‖ + ‖primitive 0‖ +
        ‖∫ time in (0 : ℝ)..terminal, differentiatedTerm time‖ +
          ‖∫ time in (0 : ℝ)..terminal, errorTerm time‖ := by
      exact (norm_add_le _ _).trans (add_le_add_right
        ((norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)) _)
    _ ≤ dilationBound * amplitudeBound / (2 * frequency) +
        dilationBound * amplitudeBound / (2 * frequency) +
        ((dilationBound * amplitudeDerivativeBound + dilationDerivativeBound * amplitudeBound) /
          (2 * frequency)) * terminal +
        (dilationBound * amplitudeBound * phaseErrorBound / frequency) * terminal := by
      exact add_le_add (add_le_add (add_le_add (primitiveBound terminal ⟨terminalNonnegative, le_rfl⟩)
        (primitiveBound 0 initialInside)) differentiatedIntegralBound) errorIntegralBound
    _ = _ := by ring

end EulerNonuniqueness
