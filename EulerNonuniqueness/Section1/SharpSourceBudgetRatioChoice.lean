import EulerNonuniqueness.General.ReciprocalPolynomialSmallness

noncomputable section

namespace EulerNonuniqueness.Paper

theorem exists_uniform_sharp_source_budget_ratio
    {incoming outgoing extent magnitude distance neutralFactor coefficient tailTolerance accuracy : ℝ}
    (incomingNonnegative : 0 ≤ incoming) (magnitudeNonnegative : 0 ≤ magnitude)
    (coefficientPositive : 0 < coefficient)
    (tailNonnegative : 0 ≤ tailTolerance) (accuracyPositive : 0 < accuracy) :
    ∃ ratioMin ≥ (2 : ℝ), ∀ ratio : ℝ, ratioMin ≤ ratio →
      4 * outgoing + 100 * (incoming * extent ^ 2 * magnitude / (coefficient * ratio ^ 2) +
        outgoing * (1 + distance + neutralFactor) / ratio) + tailTolerance / ratio ^ 2 ≤
      4 * outgoing + accuracy := by
  let quadratic := 100 * incoming * extent ^ 2 * magnitude / coefficient + tailTolerance
  let linear := 100 * outgoing * (1 + distance + neutralFactor)
  have quadraticNonnegative : 0 ≤ quadratic := by
    dsimp only [quadratic]
    exact add_nonneg (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) incomingNonnegative)
      (sq_nonneg extent)) magnitudeNonnegative) coefficientPositive.le) tailNonnegative
  obtain ⟨ratioMin, ratioTwo, estimates⟩ :=
    EulerNonuniqueness.General.exists_uniform_reciprocal_quadratic_small
      (linear := linear) quadraticNonnegative accuracyPositive
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro ratio ratioLarge
  have ratioPositive : 0 < ratio := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (ratioTwo.trans ratioLarge)
  have normalized : 4 * outgoing + 100 * (incoming * extent ^ 2 * magnitude / (coefficient * ratio ^ 2) +
      outgoing * (1 + distance + neutralFactor) / ratio) + tailTolerance / ratio ^ 2 =
      4 * outgoing + (quadratic / ratio ^ 2 + linear / ratio) := by
    dsimp only [quadratic, linear]
    field_simp [coefficientPositive.ne', ratioPositive.ne']
    ring
  rw [normalized]
  exact add_le_add_left (estimates ratio ratioLarge) _

end EulerNonuniqueness.Paper
