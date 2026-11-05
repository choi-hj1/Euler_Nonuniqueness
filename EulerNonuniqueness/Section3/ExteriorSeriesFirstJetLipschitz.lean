import EulerNonuniqueness.Section3.ExteriorSeriesCoefficientDifference
import EulerNonuniqueness.General.UniformQuadraticFirstJetLipschitz

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

theorem exteriorContourPowerSeriesFirstJet_difference_norm_le (phase : Circle) (coefficient : ℕ → ℂ)
    (first final : PeriodicC1HolderHalf) (firstBound : ‖first‖ ≤ 5 / 2) (finalBound : ‖final‖ ≤ 5 / 2)
    (weighted : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖)) :
    ‖exteriorContourPowerSeriesFirstJet phase coefficient first -
        exteriorContourPowerSeriesFirstJet phase coefficient final‖ ≤
      8 * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖) * ‖first - final‖ := by
  let constant := ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖
  have nonnegative : 0 ≤ constant := tsum_nonneg (fun degree => by positivity)
  have firstThree : ‖first‖ ≤ 3 := by linarith
  have finalThree : ‖final‖ ≤ 3 := by linarith
  by_cases close : 2 * ‖first - final‖ ≤ 1 / 2
  · have taylor (base : PeriodicC1HolderHalf) (bound : ‖base‖ ≤ 5 / 2)
        (increment : PeriodicC1HolderHalf) (small : ‖increment‖ ≤ 1 / 2) :
        ‖EulerNonuniqueness.General.linearJetTaylorError
          (exteriorContourPowerSeries phase coefficient)
          (exteriorContourPowerSeriesFirstJet phase coefficient) base increment‖ ≤ constant * ‖increment‖ ^ 2 := by
      have shifted : ‖base + increment‖ ≤ 3 := (norm_add_le _ _).trans (by linarith)
      have actual := exteriorContourPowerSeriesFirstJet_error_bound phase coefficient (base + increment) base
        shifted (by linarith) weighted
      simpa only [EulerNonuniqueness.General.linearJetTaylorError, add_sub_cancel_left] using actual
    have bound := EulerNonuniqueness.General.linear_operator_difference_le_of_uniform_quadratic
      (exteriorContourPowerSeries phase coefficient) (exteriorContourPowerSeriesFirstJet phase coefficient)
      final first nonnegative (taylor final finalBound) (taylor first firstBound) close
    exact bound.trans (by nlinarith [mul_nonneg nonnegative (norm_nonneg (first - final))])
  · have firstJet := exteriorContourPowerSeriesFirstJet_norm_bound96 phase coefficient first firstThree weighted
    have finalJet := exteriorContourPowerSeriesFirstJet_norm_bound96 phase coefficient final finalThree weighted
    have triangle := (norm_sub_le (exteriorContourPowerSeriesFirstJet phase coefficient first)
      (exteriorContourPowerSeriesFirstJet phase coefficient final)).trans (add_le_add firstJet finalJet)
    have scaled := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge close)) nonnegative
    dsimp only [constant] at *
    nlinarith

theorem exteriorContourPowerSeriesFirstJet_pair_difference_norm_le (phase : Circle)
    (initialCoefficient finalCoefficient : ℕ → ℂ) (first final : PeriodicC1HolderHalf)
    (firstBound : ‖first‖ ≤ 5 / 2) (finalBound : ‖final‖ ≤ 5 / 2)
    (initialSummable : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖))
    (finalSummable : Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖)) :
    ‖exteriorContourPowerSeriesFirstJet phase initialCoefficient first -
        exteriorContourPowerSeriesFirstJet phase finalCoefficient final‖ ≤
      8 * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) * ‖first - final‖ +
        ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖ := by
  have state := exteriorContourPowerSeriesFirstJet_difference_norm_le phase initialCoefficient first final
    firstBound finalBound initialSummable
  have coefficient := exteriorContourPowerSeriesFirstJet_coefficient_difference_norm_le phase final
    (by linarith) initialCoefficient finalCoefficient initialSummable finalSummable
  exact (norm_sub_le_norm_sub_add_norm_sub
    (exteriorContourPowerSeriesFirstJet phase initialCoefficient first)
    (exteriorContourPowerSeriesFirstJet phase initialCoefficient final)
    (exteriorContourPowerSeriesFirstJet phase finalCoefficient final)).trans (add_le_add state coefficient)

end EulerNonuniqueness.Paper
