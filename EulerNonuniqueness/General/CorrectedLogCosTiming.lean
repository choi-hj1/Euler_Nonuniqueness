import EulerNonuniqueness.General.PerturbedLogCosTiming
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
namespace EulerNonuniqueness

/-- The actual wrapped phase correction contributes explicitly to the coefficient error. -/
theorem corrected_log_cos_timing_recurrence
    {ratio current next coefficient coefficientError phaseError timingError : ℝ}
    (ratioLarge : 4 ≤ ratio) (coefficientErrorNonnegative : 0 ≤ coefficientError)
    (effectiveSmall : coefficientError + 2 * |phaseError| ≤ 1 / 8)
    (timingErrorNonnegative : 0 ≤ timingError)
    (angleSmall : |2 * (1 + ratio⁻¹) * next| ≤ 1 / 2)
    (coefficientClose : |coefficient - Real.cos (2 * (1 + ratio⁻¹) * next - 2 * phaseError)| ≤ coefficientError)
    (delayClose : |current - ratio⁻¹ * next + Real.log coefficient / (2 * Real.sqrt 2)| ≤ timingError) :
    |current| ≤ ratio⁻¹ * |next| + 4 * next ^ 2 + coefficientError + 2 * |phaseError| + timingError := by
  have cosineLipschitz : LipschitzWith 1 Real.cos := by
    apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_cos
    intro value
    apply NNReal.coe_le_coe.mp
    change ‖deriv Real.cos value‖ ≤ (1 : ℝ)
    rw [Real.deriv_cos, norm_neg, Real.norm_eq_abs]
    exact Real.abs_sin_le_one value
  have cosineDifference :
      |Real.cos (2 * (1 + ratio⁻¹) * next - 2 * phaseError) - Real.cos (2 * (1 + ratio⁻¹) * next)| ≤ 2 * |phaseError| := by
    have estimate := cosineLipschitz.dist_le_mul (2 * (1 + ratio⁻¹) * next - 2 * phaseError) (2 * (1 + ratio⁻¹) * next)
    have difference : (2 * (1 + ratio⁻¹) * next - 2 * phaseError) - 2 * (1 + ratio⁻¹) * next = -(2 * phaseError) := by ring
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, difference, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using estimate
  have effectiveClose : |coefficient - Real.cos (2 * (1 + ratio⁻¹) * next)| ≤ coefficientError + 2 * |phaseError| :=
    (abs_sub_le coefficient (Real.cos (2 * (1 + ratio⁻¹) * next - 2 * phaseError))
      (Real.cos (2 * (1 + ratio⁻¹) * next))).trans (add_le_add coefficientClose cosineDifference)
  have result := perturbed_log_cos_timing_recurrence ratioLarge
    (by positivity : 0 ≤ coefficientError + 2 * |phaseError|) effectiveSmall timingErrorNonnegative angleSmall effectiveClose delayClose
  linarith only [result]

end EulerNonuniqueness
