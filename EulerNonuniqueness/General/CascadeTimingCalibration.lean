import EulerNonuniqueness.General.CorrectedLogCosTiming

noncomputable section
namespace EulerNonuniqueness

/-- Fixed timing budgets can be chosen before any model section or coordinate map. -/
theorem cascade_timing_fixed_budgets {eta ratio : ℝ}
    (etaPositive : 0 < eta) (etaSmall : eta ≤ 1 / 1000) (ratioLarge : 4 ≤ ratio) :
    0 < eta / 100 ∧ 0 < eta / 1000 ∧ 0 < eta / 10000 ∧
    eta / 1000 + 2 * (eta / 100) ≤ 1 / 8 ∧
    3 * eta + 2 * (eta / 100) ≤ 1 / 2 ∧
    2 * (eta / 10000) ≤ (eta / 100) / 8 ∧
    2 * (eta / 10000) ≤ eta / 1000 ∧
    ∀ next : ℝ, |next| ≤ eta → |2 * (1 + ratio⁻¹) * next| ≤ 1 / 2 := by
  have ratioPositive : 0 < ratio := by linarith only [ratioLarge]
  have inverseNonnegative : 0 ≤ ratio⁻¹ := inv_nonneg.mpr ratioPositive.le
  have inverseBound : ratio⁻¹ ≤ 1 / 4 := by
    rw [← one_div]
    exact (div_le_iff₀ ratioPositive).mpr (by linarith only [ratioLarge])
  refine ⟨by positivity, by positivity, by positivity, by linarith only [etaSmall],
    by linarith only [etaSmall], by linarith only [etaPositive], by linarith only [etaPositive], ?_⟩
  intro next nextBound
  calc
    _ = 2 * (1 + ratio⁻¹) * |next| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (1 + ratio⁻¹))]
    _ ≤ (5 / 2) * eta := mul_le_mul (by linarith only [inverseBound]) nextBound (abs_nonneg _) (by norm_num)
    _ ≤ 1 / 2 := by linarith only [etaSmall]

/-- The calibrated corrected recurrence improves the next-scale bound by a factor of two. -/
theorem cascade_timing_recurrence_half_bound
    {eta ratio current next coefficientError phaseError passageError modelError : ℝ}
    (etaPositive : 0 < eta) (etaSmall : eta ≤ 1 / 1000) (ratioLarge : 4 ≤ ratio)
    (nextBound : |next| ≤ eta) (phaseBound : |phaseError| ≤ eta / 100)
    (coefficientBound : coefficientError ≤ eta / 1000)
    (passageBound : passageError ≤ eta / 1000) (modelBound : modelError ≤ eta / 1000)
    (recurrence : |current| ≤ ratio⁻¹ * |next| + 4 * next ^ 2 + coefficientError +
      2 * |phaseError| + passageError + modelError) :
    |current| ≤ eta / 2 := by
  have ratioPositive : 0 < ratio := by linarith only [ratioLarge]
  have inverseBound : ratio⁻¹ ≤ 1 / 4 := by
    rw [← one_div]
    exact (div_le_iff₀ ratioPositive).mpr (by linarith only [ratioLarge])
  have linear : ratio⁻¹ * |next| ≤ eta / 4 := by
    have bound := mul_le_mul inverseBound nextBound (abs_nonneg next) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using bound
  have square : next ^ 2 ≤ eta ^ 2 := by
    have bound := pow_le_pow_left₀ (abs_nonneg next) nextBound 2
    simpa only [sq_abs] using bound
  have smallSquare : next ^ 2 ≤ eta / 1000 := by
    have bound := mul_le_mul_of_nonneg_left etaSmall etaPositive.le
    nlinarith only [square, bound]
  linarith only [recurrence, linear, smallSquare, coefficientBound, phaseBound, passageBound, modelBound, etaPositive]

/-- A corrected logarithmic exit estimate closes with the same fixed budgets. -/
theorem calibrated_corrected_log_cos_timing_recurrence
    {eta ratio current next coefficient coefficientError phaseError passageError modelError : ℝ}
    (etaPositive : 0 < eta) (etaSmall : eta ≤ 1 / 1000) (ratioLarge : 4 ≤ ratio)
    (nextBound : |next| ≤ eta) (phaseBound : |phaseError| ≤ eta / 100)
    (coefficientBound : coefficientError ≤ eta / 1000)
    (passageBound : passageError ≤ eta / 1000) (modelBound : modelError ≤ eta / 1000)
    (coefficientClose : |coefficient - Real.cos (2 * (1 + ratio⁻¹) * next - 2 * phaseError)| ≤ coefficientError)
    (delayClose : |current - ratio⁻¹ * next + Real.log coefficient / (2 * Real.sqrt 2)| ≤ passageError + modelError) :
    |current| ≤ eta / 2 := by
  have budgets := cascade_timing_fixed_budgets etaPositive etaSmall ratioLarge
  have coefficientNonnegative : 0 ≤ coefficientError := (abs_nonneg _).trans coefficientClose
  have effectiveSmall : coefficientError + 2 * |phaseError| ≤ 1 / 8 := by
    linarith only [coefficientBound, phaseBound, budgets.2.2.2.1]
  have timingNonnegative : 0 ≤ passageError + modelError := (abs_nonneg _).trans delayClose
  have recurrence := corrected_log_cos_timing_recurrence ratioLarge coefficientNonnegative effectiveSmall timingNonnegative
    (budgets.2.2.2.2.2.2.2 next nextBound) coefficientClose delayClose
  apply cascade_timing_recurrence_half_bound etaPositive etaSmall ratioLarge nextBound phaseBound coefficientBound passageBound modelBound
  linarith only [recurrence]

end EulerNonuniqueness
