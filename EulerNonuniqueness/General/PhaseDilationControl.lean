import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set

namespace EulerNonuniqueness

theorem phase_dilation_increment_bound
    {phase dilation remainder : ℝ → ℝ} {frequency terminal strain dilationConstant remainderConstant : ℝ}
    (frequencyPositive : 0 < frequency) (terminalNonnegative : 0 ≤ terminal)
    (strainNonnegative : 0 ≤ strain) (dilationNonnegative : 0 ≤ dilationConstant)
    (remainderNonnegative : 0 ≤ remainderConstant)
    (equation : ∀ time ∈ Icc 0 terminal,
      HasDerivAt phase (-frequency / dilation time + remainder time) time)
    (lower : ∀ time ∈ Icc 0 terminal, 1 / 2 ≤ dilation time)
    (dilationBound : ∀ time ∈ Icc 0 terminal, |dilation time - 1| ≤
      dilationConstant * ((strain + terminal * strain ^ 2) / frequency + frequency⁻¹ ^ 5))
    (remainderBound : ∀ time ∈ Icc 0 terminal,
      |remainder time| ≤ remainderConstant * (strain + frequency⁻¹ ^ 4)) :
    |phase terminal - phase 0 + frequency * terminal| ≤
      (2 * dilationConstant + remainderConstant) * terminal * (strain + terminal * strain ^ 2 + frequency⁻¹ ^ 4) := by
  let rate := (strain + terminal * strain ^ 2) / frequency + frequency⁻¹ ^ 5
  let budget := strain + terminal * strain ^ 2 + frequency⁻¹ ^ 4
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have budgetNonnegative : 0 ≤ budget := by dsimp only [budget]; positivity
  have rateIdentity : frequency * rate = budget := by
    dsimp only [rate, budget]
    field_simp [frequencyPositive.ne']
    <;> ring
  have baseBound : strain + frequency⁻¹ ^ 4 ≤ budget := by
    dsimp only [budget]
    nlinarith only [mul_nonneg terminalNonnegative (sq_nonneg strain)]
  have slope (time : ℝ) (member : time ∈ Icc 0 terminal) :
      |(-frequency / dilation time + remainder time) + frequency| ≤
        (2 * dilationConstant + remainderConstant) * budget := by
    have dilationPositive : 0 < dilation time := by linarith [lower time member]
    have inverseError : |-frequency / dilation time + frequency| ≤ 2 * frequency * dilationConstant * rate := by
      have identity : -frequency / dilation time + frequency = frequency * (dilation time - 1) / dilation time := by
        field_simp [dilationPositive.ne']
        <;> ring
      rw [identity, abs_div, abs_mul, abs_of_pos frequencyPositive, abs_of_pos dilationPositive]
      apply (div_le_iff₀ dilationPositive).mpr
      have actual := mul_le_mul_of_nonneg_left (dilationBound time member) frequencyPositive.le
      change frequency * |dilation time - 1| ≤ frequency * (dilationConstant * rate) at actual
      have half := mul_le_mul_of_nonneg_left (lower time member)
        (by positivity : 0 ≤ 2 * frequency * dilationConstant * rate)
      calc
        _ ≤ frequency * (dilationConstant * rate) := actual
        _ = 2 * frequency * dilationConstant * rate * (1 / 2) := by ring
        _ ≤ _ := half
    have arrangement : (-frequency / dilation time + remainder time) + frequency =
        (-frequency / dilation time + frequency) + remainder time := by ring
    rw [arrangement]
    apply (abs_add _ _).trans
    apply (add_le_add inverseError (remainderBound time member)).trans
    have second := mul_le_mul_of_nonneg_left baseBound remainderNonnegative
    have firstIdentity : 2 * frequency * dilationConstant * rate = 2 * dilationConstant * budget := by
      rw [← rateIdentity]
      ring
    rw [firstIdentity]
    nlinarith only [second]
  have derivative (time : ℝ) (member : time ∈ Icc 0 terminal) :
      HasDerivWithinAt (fun current => phase current + frequency * current)
        ((-frequency / dilation time + remainder time) + frequency) (Icc 0 terminal) time := by
    simpa only [mul_one] using ((equation time member).add ((hasDerivAt_id time).const_mul frequency)).hasDerivWithinAt
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment' derivative
    (fun time member => by rw [Real.norm_eq_abs]; exact slope time ⟨member.1, member.2.le⟩)
    terminal ⟨terminalNonnegative, le_rfl⟩
  simp only [Real.norm_eq_abs, mul_zero, add_zero] at estimate
  have arrangement : phase terminal + frequency * terminal - phase 0 = phase terminal - phase 0 + frequency * terminal := by ring
  rw [arrangement] at estimate
  convert estimate using 1 <;> dsimp only [budget] <;> ring

end EulerNonuniqueness
