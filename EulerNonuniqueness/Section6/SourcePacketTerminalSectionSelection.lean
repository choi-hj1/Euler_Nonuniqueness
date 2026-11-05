import EulerNonuniqueness.Section6.ArbitraryOutgoingSection

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

/-- Choose the terminal model section with the numerical accuracy needed by the signed source window. -/
theorem normalizedSeparatingOrbit_terminal_signed_section (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) {tolerance : ℝ}
    (tolerancePositive : 0 < tolerance) :
    ∃ sectionTime > (0 : ℝ), ∃ initialError > (0 : ℝ), initialError ≤ 1 / 64 ∧
      2048 ≤ separationRadius orbit sectionTime ∧
      ‖orbit.positive sectionTime + orbit.negative sectionTime -
        Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ initialError / 2 ∧
      (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
        (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
          (orbit.positive sectionTime - orbit.negative sectionTime)).re ∧
      20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤
        min (tolerance / 4) 1 / 5120 := by
  let budget := min (tolerance / 4) 1 / 5120
  have budgetPositive : 0 < budget := by dsimp only [budget]; positivity
  let initialError := min (1 / 64) (budget / 40)
  have errorPositive : 0 < initialError := by dsimp only [initialError]; positivity
  have errorSmall : initialError ≤ 1 / 64 := min_le_left _ _
  have errorBudget : 20 * initialError ≤ budget / 2 := by
    have bound : initialError ≤ budget / 40 := min_le_right _ _
    linarith only [bound]
  obtain ⟨sectionTime, timePositive, radiusBound, close, outgoing⟩ :=
    normalizedSeparatingOrbit_arbitrary_outgoing_section orbit normalized
      (tolerance := initialError / 2) (by positivity) (max 2048 (166400 / budget + 1))
  have radiusLarge : 2048 ≤ separationRadius orbit sectionTime :=
    (le_max_left _ _).trans ((le_max_right _ _).trans radiusBound)
  have radiusBudget : 166400 / budget + 1 ≤ separationRadius orbit sectionTime :=
    (le_max_right _ _).trans ((le_max_right _ _).trans radiusBound)
  have radiusPositive : 0 < separationRadius orbit sectionTime := by linarith only [radiusLarge]
  have radiusOne : 1 ≤ separationRadius orbit sectionTime := by linarith only [radiusLarge]
  have budgetProduct : 166400 ≤ budget * separationRadius orbit sectionTime := by
    have lower : 166400 / budget ≤ separationRadius orbit sectionTime := by
      linarith only [radiusBudget]
    exact (div_le_iff₀ budgetPositive).mp lower |>.trans_eq (mul_comm _ _)
  have radiusSquare : separationRadius orbit sectionTime ≤ separationRadius orbit sectionTime ^ 2 := by
    nlinarith only [radiusOne]
  have squareBudget : 166400 ≤ budget * separationRadius orbit sectionTime ^ 2 :=
    budgetProduct.trans (mul_le_mul_of_nonneg_left radiusSquare budgetPositive.le)
  have reciprocalBudget : 83200 / separationRadius orbit sectionTime ^ 2 ≤ budget / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos radiusPositive)).mpr
    nlinarith only [squareBudget]
  refine ⟨sectionTime, timePositive, initialError, errorPositive, errorSmall, radiusLarge, close, outgoing, ?_⟩
  change 20 * initialError + 83200 / separationRadius orbit sectionTime ^ 2 ≤ budget
  linarith only [errorBudget, reciprocalBudget]

end EulerNonuniqueness.Section6
