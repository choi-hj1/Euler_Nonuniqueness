import EulerNonuniqueness.General.InteriorDerivativeError
import EulerNonuniqueness.General.OscillatoryCancellation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness

theorem interior_oscillatory_cancellation_norm_le
    {amplitude amplitudeDerivative : ℝ → ℂ}
    {dilation dilationDerivative phase phaseError : ℝ → ℝ}
    {frequency terminal dilationBound amplitudeBound amplitudeDerivativeBound
      dilationDerivativeBound phaseErrorBound : ℝ}
    (frequencyPositive : 0 < frequency) (terminalNonnegative : 0 ≤ terminal)
    (dilationBoundNonnegative : 0 ≤ dilationBound) (amplitudeBoundNonnegative : 0 ≤ amplitudeBound)
    (amplitudeDerivativeBoundNonnegative : 0 ≤ amplitudeDerivativeBound)
    (dilationDerivativeBoundNonnegative : 0 ≤ dilationDerivativeBound)
    (phaseErrorBoundNonnegative : 0 ≤ phaseErrorBound)
    (amplitudeContinuous : ContinuousOn amplitude (Icc 0 terminal))
    (dilationContinuous : ContinuousOn dilation (Icc 0 terminal))
    (phaseContinuous : ContinuousOn phase (Icc 0 terminal))
    (amplitudeEquation : ∀ time ∈ Ioo 0 terminal, HasDerivAt amplitude (amplitudeDerivative time) time)
    (dilationEquation : ∀ time ∈ Ioo 0 terminal, HasDerivAt dilation (dilationDerivative time) time)
    (phaseEquation : ∀ time ∈ Ioo 0 terminal,
      HasDerivAt phase (-frequency / dilation time + phaseError time) time)
    (dilationNonzero : ∀ time ∈ Ioo 0 terminal, dilation time ≠ 0)
    (dilationControl : ∀ time ∈ Icc 0 terminal, |dilation time| ≤ dilationBound)
    (amplitudeControl : ∀ time ∈ Icc 0 terminal, ‖amplitude time‖ ≤ amplitudeBound)
    (amplitudeDerivativeControl : ∀ time ∈ Ioo 0 terminal, ‖amplitudeDerivative time‖ ≤ amplitudeDerivativeBound)
    (dilationDerivativeControl : ∀ time ∈ Ioo 0 terminal, |dilationDerivative time| ≤ dilationDerivativeBound)
    (phaseErrorControl : ∀ time ∈ Ioo 0 terminal, |phaseError time| ≤ phaseErrorBound) :
    ‖∫ time in (0 : ℝ)..terminal,
      amplitude time * Complex.exp (-2 * Complex.I * (phase time : ℂ))‖ ≤
      (2 * dilationBound * amplitudeBound + terminal *
        (dilationBound * amplitudeDerivativeBound + dilationDerivativeBound * amplitudeBound +
          2 * dilationBound * amplitudeBound * phaseErrorBound)) / (2 * frequency) := by
  let oscillation := fun time => Complex.exp (-2 * Complex.I * (phase time : ℂ))
  let main := fun time => amplitude time * oscillation time
  let differentiated := fun time =>
    ((dilation time : ℂ) * amplitudeDerivative time + (dilationDerivative time : ℂ) * amplitude time) *
      oscillation time / (2 * Complex.I * (frequency : ℂ))
  let error := fun time => (dilation time : ℂ) * amplitude time * (phaseError time : ℂ) *
    oscillation time / (frequency : ℂ)
  let primitive := fun time => (dilation time : ℂ) * amplitude time * oscillation time /
    (2 * Complex.I * (frequency : ℂ))
  let rate := (dilationBound * amplitudeDerivativeBound + dilationDerivativeBound * amplitudeBound) / (2 * frequency) +
    dilationBound * amplitudeBound * phaseErrorBound / frequency
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have oscillationContinuous : ContinuousOn oscillation (Icc 0 terminal) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn phaseContinuous))
  have mainContinuous : ContinuousOn main (Icc 0 terminal) := amplitudeContinuous.mul oscillationContinuous
  have primitiveContinuous : ContinuousOn primitive (Icc 0 terminal) :=
    (((Complex.continuous_ofReal.comp_continuousOn dilationContinuous).mul amplitudeContinuous).mul
      oscillationContinuous).div_const _
  have denominatorNorm : ‖(2 : ℂ) * Complex.I * (frequency : ℂ)‖ = 2 * frequency := by
    simp [norm_mul, abs_of_pos frequencyPositive]
  have frequencyNorm : ‖(frequency : ℂ)‖ = frequency := by simp [abs_of_pos frequencyPositive]
  have primitiveBound (time : ℝ) (inside : time ∈ Icc 0 terminal) :
      ‖primitive time‖ ≤ dilationBound * amplitudeBound / (2 * frequency) := by
    dsimp only [primitive, oscillation]
    rw [norm_div, norm_mul, norm_mul, norm_exp_negative_two_mul_I, mul_one, denominatorNorm,
      Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (dilationControl time inside) (amplitudeControl time inside)
        (norm_nonneg _) dilationBoundNonnegative) (by positivity)
  have primitiveDerivative (time : ℝ) (inside : time ∈ Ioo 0 terminal) :
      HasDerivAt primitive (main time + differentiated time - error time) time := by
    have exponential := ((phaseEquation time inside).ofReal_comp.const_mul (-2 * Complex.I)).cexp
    have actual := ((((dilationEquation time inside).ofReal_comp.mul (amplitudeEquation time inside)).mul
      exponential).div_const (2 * Complex.I * (frequency : ℂ)))
    convert actual using 1
    dsimp only [primitive, main, differentiated, error, oscillation]
    push_cast
    have frequencyNonzero : (frequency : ℂ) ≠ 0 := by exact_mod_cast frequencyPositive.ne'
    have dilationNotZero : (dilation time : ℂ) ≠ 0 := by exact_mod_cast dilationNonzero time inside
    field_simp
    ring
  have derivativeError (time : ℝ) (inside : time ∈ Ioo 0 terminal) :
      ‖(main time + differentiated time - error time) - main time‖ ≤ rate := by
    have closed : time ∈ Icc 0 terminal := ⟨inside.1.le, inside.2.le⟩
    have differentiatedBound : ‖differentiated time‖ ≤
        (dilationBound * amplitudeDerivativeBound + dilationDerivativeBound * amplitudeBound) / (2 * frequency) := by
      dsimp only [differentiated, oscillation]
      rw [norm_div, norm_mul, norm_exp_negative_two_mul_I, mul_one, denominatorNorm]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_mul (dilationControl time closed) (amplitudeDerivativeControl time inside)
          (norm_nonneg _) dilationBoundNonnegative)
        (mul_le_mul (dilationDerivativeControl time inside) (amplitudeControl time closed)
          (norm_nonneg _) dilationDerivativeBoundNonnegative)
    have errorBound : ‖error time‖ ≤ dilationBound * amplitudeBound * phaseErrorBound / frequency := by
      dsimp only [error, oscillation]
      rw [norm_div, norm_mul, norm_mul, norm_mul, norm_exp_negative_two_mul_I, mul_one, frequencyNorm,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      apply div_le_div_of_nonneg_right _ frequencyPositive.le
      exact mul_le_mul
        (mul_le_mul (dilationControl time closed) (amplitudeControl time closed) (norm_nonneg _) dilationBoundNonnegative)
        (phaseErrorControl time inside) (abs_nonneg _) (mul_nonneg dilationBoundNonnegative amplitudeBoundNonnegative)
    have identity : (main time + differentiated time - error time) - main time = differentiated time - error time := by abel
    rw [identity]
    exact (norm_sub_le _ _).trans (add_le_add differentiatedBound errorBound)
  have integrated := norm_sub_integral_le_of_interior_derivative_error terminalNonnegative rateNonnegative
    primitiveContinuous primitiveDerivative mainContinuous derivativeError
  have rearrange : (∫ time in (0 : ℝ)..terminal, main time) = primitive terminal - primitive 0 -
      (primitive terminal - primitive 0 - ∫ time in (0 : ℝ)..terminal, main time) := by abel
  change ‖∫ time in (0 : ℝ)..terminal, main time‖ ≤ _
  rw [rearrange]
  apply (norm_sub_le _ _).trans
  apply (add_le_add_right (norm_sub_le _ _) _).trans
  apply (add_le_add (add_le_add (primitiveBound terminal ⟨terminalNonnegative, le_rfl⟩)
    (primitiveBound 0 ⟨le_rfl, terminalNonnegative⟩)) integrated).trans_eq
  dsimp only [rate]
  ring

end EulerNonuniqueness
