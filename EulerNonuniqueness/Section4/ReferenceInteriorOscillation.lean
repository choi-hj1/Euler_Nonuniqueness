import EulerNonuniqueness.General.InteriorOscillatoryCancellation

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

theorem reference_interior_oscillatory_strain_bound
    {strain strainDerivative : ℝ → ℂ}
    {dilation dilationDerivative phase phaseError : ℝ → ℝ}
    {frequency terminal strainBound constant : ℝ}
    (frequencyPositive : 0 < frequency) (terminalNonnegative : 0 ≤ terminal)
    (strainNonnegative : 0 ≤ strainBound) (strainSmall : strainBound ≤ 1) (constantLarge : 1 ≤ constant)
    (strainContinuous : ContinuousOn strain (Icc 0 terminal))
    (dilationContinuous : ContinuousOn dilation (Icc 0 terminal))
    (phaseContinuous : ContinuousOn phase (Icc 0 terminal))
    (strainEquation : ∀ time ∈ Ioo 0 terminal, HasDerivAt strain (strainDerivative time) time)
    (dilationEquation : ∀ time ∈ Ioo 0 terminal, HasDerivAt dilation (dilationDerivative time) time)
    (phaseEquation : ∀ time ∈ Ioo 0 terminal,
      HasDerivAt phase (-frequency / dilation time + phaseError time) time)
    (dilationNonzero : ∀ time ∈ Ioo 0 terminal, dilation time ≠ 0)
    (dilationControl : ∀ time ∈ Icc 0 terminal, |dilation time| ≤ 2)
    (strainControl : ∀ time ∈ Icc 0 terminal, ‖strain time‖ ≤ constant * strainBound)
    (strainDerivativeControl : ∀ time ∈ Ioo 0 terminal,
      ‖strainDerivative time‖ ≤ constant * (strainBound ^ 2 + frequency⁻¹ ^ 4))
    (dilationDerivativeControl : ∀ time ∈ Ioo 0 terminal,
      |dilationDerivative time| ≤ 2 * constant * (strainBound + frequency⁻¹ ^ 4))
    (phaseErrorControl : ∀ time ∈ Ioo 0 terminal,
      |phaseError time| ≤ constant * (strainBound + frequency⁻¹ ^ 4)) :
    ‖∫ time in (0 : ℝ)..terminal, strain time * Complex.exp (-2 * Complex.I * (phase time : ℂ))‖ ≤
      8 * constant ^ 2 * ((strainBound + terminal * strainBound ^ 2) / frequency +
        terminal * frequency⁻¹ ^ 5) := by
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantLarge
  have bound := interior_oscillatory_cancellation_norm_le frequencyPositive terminalNonnegative
    (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg constantPositive.le strainNonnegative)
    (by positivity : 0 ≤ constant * (strainBound ^ 2 + frequency⁻¹ ^ 4))
    (by positivity : 0 ≤ 2 * constant * (strainBound + frequency⁻¹ ^ 4))
    (by positivity : 0 ≤ constant * (strainBound + frequency⁻¹ ^ 4))
    strainContinuous dilationContinuous phaseContinuous
    strainEquation dilationEquation phaseEquation dilationNonzero dilationControl strainControl
    strainDerivativeControl dilationDerivativeControl phaseErrorControl
  apply bound.trans
  have constantSquareBound : constant ≤ constant ^ 2 := by nlinarith
  have errorNonnegative : 0 ≤ frequency⁻¹ ^ 4 := by positivity
  have mixedBound : strainBound * frequency⁻¹ ^ 4 ≤ frequency⁻¹ ^ 4 := by
    exact (mul_le_mul_of_nonneg_right strainSmall errorNonnegative).trans_eq (one_mul _)
  have simplified :
      (2 * 2 * (constant * strainBound) + terminal *
        (2 * (constant * (strainBound ^ 2 + frequency⁻¹ ^ 4)) +
          (2 * constant * (strainBound + frequency⁻¹ ^ 4)) * (constant * strainBound) +
          2 * 2 * (constant * strainBound) * (constant * (strainBound + frequency⁻¹ ^ 4)))) /
          (2 * frequency) ≤
        8 * constant ^ 2 * ((strainBound + terminal * strainBound ^ 2) / frequency +
          terminal * (frequency⁻¹ ^ 4 / frequency)) := by
    apply (div_le_iff₀ (show 0 < 2 * frequency by positivity)).mpr
    have rightIdentity :
        8 * constant ^ 2 * ((strainBound + terminal * strainBound ^ 2) / frequency +
          terminal * (frequency⁻¹ ^ 4 / frequency)) * (2 * frequency) =
        16 * constant ^ 2 * (strainBound + terminal * (strainBound ^ 2 + frequency⁻¹ ^ 4)) := by
      field_simp
      ring
    rw [rightIdentity]
    have firstBound := mul_le_mul_of_nonneg_right constantSquareBound strainNonnegative
    have secondBound := mul_le_mul_of_nonneg_right constantSquareBound (sq_nonneg strainBound)
    have thirdBound := mul_le_mul_of_nonneg_right constantSquareBound errorNonnegative
    have fourthBound := mul_le_mul_of_nonneg_left mixedBound (show 0 ≤ constant ^ 2 by positivity)
    have timeBound := mul_le_mul_of_nonneg_left
      (show 2 * constant * (strainBound ^ 2 + frequency⁻¹ ^ 4) +
          6 * constant ^ 2 * strainBound * (strainBound + frequency⁻¹ ^ 4) ≤
        16 * constant ^ 2 * (strainBound ^ 2 + frequency⁻¹ ^ 4) by
        nlinarith [mul_nonneg (sq_nonneg constant) (sq_nonneg strainBound)]) terminalNonnegative
    nlinarith
  have inverseIdentity : frequency⁻¹ ^ 4 / frequency = frequency⁻¹ ^ 5 := by
    rw [div_eq_mul_inv]
    ring
  simpa only [inverseIdentity] using simplified

end EulerNonuniqueness.Paper
