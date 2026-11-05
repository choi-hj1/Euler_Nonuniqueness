import EulerNonuniqueness.Section6.ExteriorTaylorTailDilation

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem exteriorTaylorCoefficient_pair_norm_radius_mono {firstCount secondCount : ℕ}
    (first : FiniteMovingPatchFamily firstCount) (second : FiniteMovingPatchFamily secondCount)
    (firstSelected : Finset (Fin firstCount)) (secondSelected : Finset (Fin secondCount))
    (firstCenter secondCenter : ℝ → ℂ) {radius largerRadius : ℝ}
    (radiusNonnegative : 0 ≤ radius) (radiusBound : radius ≤ largerRadius)
    (degree : ℕ) (time : ℝ) :
    ‖first.exteriorTaylorCoefficient firstSelected firstCenter radius (degree + 1) time -
      second.exteriorTaylorCoefficient secondSelected secondCenter radius (degree + 1) time‖ ≤
    ‖first.exteriorTaylorCoefficient firstSelected firstCenter largerRadius (degree + 1) time -
      second.exteriorTaylorCoefficient secondSelected secondCenter largerRadius (degree + 1) time‖ := by
  have normalized (value : ℝ) :
      first.exteriorTaylorCoefficient firstSelected firstCenter value (degree + 1) time -
        second.exteriorTaylorCoefficient secondSelected secondCenter value (degree + 1) time =
      value ^ degree • (first.exteriorTaylorCoefficient firstSelected firstCenter 1 (degree + 1) time -
        second.exteriorTaylorCoefficient secondSelected secondCenter 1 (degree + 1) time) := by
    simpa only [mul_one, smul_sub] using congrArg₂ (fun firstValue secondValue : ℂ => firstValue - secondValue)
      (first.exteriorTaylorCoefficient_radius_mul firstSelected firstCenter 1 value degree time)
      (second.exteriorTaylorCoefficient_radius_mul secondSelected secondCenter 1 value degree time)
  rw [normalized radius, normalized largerRadius, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg radiusNonnegative degree),
    abs_of_nonneg (pow_nonneg (radiusNonnegative.trans radiusBound) degree)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ radiusNonnegative radiusBound degree) (norm_nonneg _)

theorem exteriorTaylorCoefficient_pair_weighted_series_radius_mono {firstCount secondCount : ℕ}
    (first : FiniteMovingPatchFamily firstCount) (second : FiniteMovingPatchFamily secondCount)
    (firstSelected : Finset (Fin firstCount)) (secondSelected : Finset (Fin secondCount))
    (firstCenter secondCenter : ℝ → ℂ) {radius largerRadius weight : ℝ}
    (radiusNonnegative : 0 ≤ radius) (radiusBound : radius ≤ largerRadius)
    (weightNonnegative : 0 ≤ weight) (time : ℝ)
    (summable : Summable (fun degree : ℕ => weight ^ (degree + 1) *
      ‖first.exteriorTaylorCoefficient firstSelected firstCenter largerRadius (degree + 1) time -
        second.exteriorTaylorCoefficient secondSelected secondCenter largerRadius (degree + 1) time‖)) :
    Summable (fun degree : ℕ => weight ^ (degree + 1) *
      ‖first.exteriorTaylorCoefficient firstSelected firstCenter radius (degree + 1) time -
        second.exteriorTaylorCoefficient secondSelected secondCenter radius (degree + 1) time‖) ∧
    (∑' degree : ℕ, weight ^ (degree + 1) *
      ‖first.exteriorTaylorCoefficient firstSelected firstCenter radius (degree + 1) time -
        second.exteriorTaylorCoefficient secondSelected secondCenter radius (degree + 1) time‖) ≤
    (∑' degree : ℕ, weight ^ (degree + 1) *
      ‖first.exteriorTaylorCoefficient firstSelected firstCenter largerRadius (degree + 1) time -
        second.exteriorTaylorCoefficient secondSelected secondCenter largerRadius (degree + 1) time‖) := by
  have pointwise (degree : ℕ) := mul_le_mul_of_nonneg_left
    (first.exteriorTaylorCoefficient_pair_norm_radius_mono second firstSelected secondSelected
      firstCenter secondCenter radiusNonnegative radiusBound degree time)
    (pow_nonneg weightNonnegative (degree + 1))
  have actual := Summable.of_nonneg_of_le (fun degree => by positivity) pointwise summable
  exact ⟨actual, actual.tsum_le_tsum pointwise summable⟩

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
