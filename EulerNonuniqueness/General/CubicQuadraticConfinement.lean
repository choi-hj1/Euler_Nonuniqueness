import EulerNonuniqueness.General.CoupledUpperRightBootstrap

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space Target : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem cubic_quadratic_two_curve_confinement
    {transverse : ℝ → Space} {neutral : ℝ → Target}
    {terminal radius neutralRadius epsilon constant : ℝ}
    (terminalNonnegative : 0 ≤ terminal) (radiusPositive : 0 < radius) (radiusSmall : radius ≤ 1)
    (neutralRadiusPositive : 0 < neutralRadius) (constantNonnegative : 0 ≤ constant)
    (forcingScale : epsilon ^ 2 ≤ radius ^ 3)
    (transverseContinuous : ContinuousOn transverse (Icc 0 terminal))
    (neutralContinuous : ContinuousOn neutral (Icc 0 terminal))
    (transverseInitial : ‖transverse 0‖ ≤ radius / 4) (neutralInitial : neutral 0 = 0)
    (budget : 8 * constant * terminal * radius ^ 2 < min 1 neutralRadius)
    (transverseSlopes : ∀ base ∈ Ico 0 terminal,
      (∀ current ∈ Icc 0 base, ‖transverse current‖ ≤ radius ∧ ‖neutral current‖ ≤ neutralRadius) →
      ∀ threshold, constant * (‖transverse base‖ ^ 3 + epsilon ^ 2) < threshold →
        ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖transverse current‖) base later < threshold)
    (neutralSlopes : ∀ base ∈ Ico 0 terminal,
      (∀ current ∈ Icc 0 base, ‖transverse current‖ ≤ radius ∧ ‖neutral current‖ ≤ neutralRadius) →
      ∀ threshold, constant * (‖transverse base‖ ^ 2 + epsilon ^ 2) < threshold →
        ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖neutral current‖) base later < threshold) :
    ∀ time ∈ Icc 0 terminal,
      ‖transverse time‖ < radius / 2 ∧ ‖neutral time‖ < neutralRadius / 4 := by
  have firstRateNonnegative : 0 ≤ 2 * constant * radius ^ 3 := by positivity
  have secondRateNonnegative : 0 ≤ 2 * constant * radius ^ 2 := by positivity
  have firstBudget := budget.trans_le (min_le_left 1 neutralRadius)
  have secondBudget := budget.trans_le (min_le_right 1 neutralRadius)
  have transverseTravel : (2 * constant * radius ^ 3) * terminal < radius / 4 := by
    have scaled := mul_lt_mul_of_pos_right firstBudget radiusPositive
    nlinarith
  have neutralTravel : (2 * constant * radius ^ 2) * terminal < neutralRadius / 4 := by
    nlinarith
  have cubicSmall : radius ^ 3 ≤ radius ^ 2 := by
    have weighted := mul_nonneg (sq_nonneg radius) (sub_nonneg.mpr radiusSmall)
    nlinarith
  have bounds := two_curve_norm_bootstrap_of_upper_right_slopes terminalNonnegative
    transverseContinuous neutralContinuous firstRateNonnegative secondRateNonnegative
    (show ‖transverse 0‖ + (2 * constant * radius ^ 3) * terminal < radius by linarith)
    (show ‖neutral 0‖ + (2 * constant * radius ^ 2) * terminal < neutralRadius by
      rw [neutralInitial, norm_zero]
      linarith)
    (by
      intro base inside history threshold strict
      have bound := (history base ⟨inside.1, le_rfl⟩).1
      have cubicBound : ‖transverse base‖ ^ 3 ≤ radius ^ 3 := by gcongr
      have rateBound : constant * (‖transverse base‖ ^ 3 + epsilon ^ 2) ≤
          2 * constant * radius ^ 3 := by
        calc
          _ ≤ constant * (radius ^ 3 + radius ^ 3) :=
            mul_le_mul_of_nonneg_left (add_le_add cubicBound forcingScale) constantNonnegative
          _ = _ := by ring
      exact transverseSlopes base inside history threshold (rateBound.trans_lt strict))
    (by
      intro base inside history threshold strict
      have bound := (history base ⟨inside.1, le_rfl⟩).1
      have squareBound : ‖transverse base‖ ^ 2 ≤ radius ^ 2 := by gcongr
      have rateBound : constant * (‖transverse base‖ ^ 2 + epsilon ^ 2) ≤
          2 * constant * radius ^ 2 := by
        calc
          _ ≤ constant * (radius ^ 2 + radius ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add squareBound (forcingScale.trans cubicSmall)) constantNonnegative
          _ = _ := by ring
      exact neutralSlopes base inside history threshold (rateBound.trans_lt strict))
  intro time inside
  have actual := bounds time inside
  have transverseTime := mul_le_mul_of_nonneg_left inside.2 firstRateNonnegative
  have neutralTime := mul_le_mul_of_nonneg_left inside.2 secondRateNonnegative
  rw [neutralInitial, norm_zero, zero_add] at actual
  exact ⟨by linarith [actual.1], by linarith [actual.2]⟩

end EulerNonuniqueness.General
