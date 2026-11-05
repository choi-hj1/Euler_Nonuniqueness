import EulerNonuniqueness.Section3.ProjectedExteriorSeriesRelativeIncrement
import EulerNonuniqueness.General.AffineResidualRelativeRemainder

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace
  gaugeOperatorUniformSecondGroup

theorem circleBasedProjectedExteriorSeries_exists_pair_value_bounds :
    ∃ radius > 0, radius ≤ 1 / 6 ∧ ∃ constant ≥ 0,
      (∀ (phase : Circle) (coefficient : ℕ → ℂ),
        Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖) →
        ∀ increment : PeriodicC1HolderHalf, ‖increment‖ ≤ radius →
        ‖circleBasedProjectedExteriorSeries phase coefficient increment‖ ≤
          constant * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖)) ∧
      ∀ (phase : Circle) (initialCoefficient finalCoefficient : ℕ → ℂ),
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) →
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖) →
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ radius → ‖final‖ ≤ radius →
      ‖circleBasedProjectedExteriorSeries phase initialCoefficient first -
        circleBasedProjectedExteriorSeries phase finalCoefficient final‖ ≤ constant *
        (((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) +
            (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖)) * ‖first - final‖ +
          ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖) := by
  obtain ⟨radius, positive, smallRadius, constant, one, absolute, difference, _⟩ :=
    circleBasedCentroidProjection_exists_uniform_firstJet_bounds
  have nonnegative : 0 ≤ constant := le_trans (by norm_num) one
  have shapeBound (point : PeriodicC1HolderHalf) (inside : ‖point‖ ≤ radius) :
      ‖standardCircleBanach + point‖ ≤ 3 :=
    (norm_add_le _ _).trans (by linarith [standardCircleBanach_norm_bound])
  refine ⟨radius, positive, smallRadius, 2 * constant, by positivity, ?_, ?_⟩
  · intro phase coefficient weighted increment inside
    have operator := (absolute increment inside).1
    have value := exteriorContourPowerSeries_norm_bound phase coefficient (standardCircleBanach + increment)
      (shapeBound increment inside) weighted
    have estimate := ((circleBasedCentroidProjection increment).le_opNorm _).trans
      (mul_le_mul operator value (norm_nonneg _) nonnegative)
    change ‖circleBasedCentroidProjection increment
      (exteriorContourPowerSeries phase coefficient (standardCircleBanach + increment))‖ ≤ _
    apply estimate.trans
    have weightNonnegative : 0 ≤ ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖ :=
      tsum_nonneg (fun degree => by positivity)
    nlinarith
  · intro phase initialCoefficient finalCoefficient initialSummable finalSummable first final firstInside finalInside
    have operator := (absolute first firstInside).1
    have operators := difference first final firstInside finalInside
    have rawAbsolute := exteriorContourPowerSeries_norm_bound phase finalCoefficient (standardCircleBanach + final)
      (shapeBound final finalInside) finalSummable
    have small : ‖(standardCircleBanach + first) - (standardCircleBanach + final)‖ ≤ 1 := by
      rw [add_sub_add_left_eq_sub]
      have bound := norm_sub_le first final
      linarith
    have rawState := exteriorContourPowerSeries_difference_bound phase initialCoefficient
      (standardCircleBanach + first) (standardCircleBanach + final)
      (shapeBound first firstInside) (shapeBound final finalInside) small initialSummable
    rw [add_sub_add_left_eq_sub] at rawState
    have rawCoefficient := exteriorContourPowerSeries_coefficient_difference_norm_le phase
      (standardCircleBanach + final) (shapeBound final finalInside) initialCoefficient finalCoefficient initialSummable finalSummable
    have rawTriangle := norm_sub_le_norm_sub_add_norm_sub
      (exteriorContourPowerSeries phase initialCoefficient (standardCircleBanach + first))
      (exteriorContourPowerSeries phase initialCoefficient (standardCircleBanach + final))
      (exteriorContourPowerSeries phase finalCoefficient (standardCircleBanach + final))
    have rawDifference := rawTriangle.trans (add_le_add rawState rawCoefficient)
    let firstRaw := exteriorContourPowerSeries phase initialCoefficient (standardCircleBanach + first)
    let finalRaw := exteriorContourPowerSeries phase finalCoefficient (standardCircleBanach + final)
    have vector : ‖circleBasedCentroidProjection first firstRaw - circleBasedCentroidProjection final finalRaw‖ ≤
        ‖circleBasedCentroidProjection first‖ * ‖firstRaw - finalRaw‖ +
          ‖circleBasedCentroidProjection first - circleBasedCentroidProjection final‖ * ‖finalRaw‖ := by
      with_reducible_and_instances
        exact EulerNonuniqueness.General.norm_operator_apply_difference_le
          (circleBasedCentroidProjection first) (circleBasedCentroidProjection final) firstRaw finalRaw
    have sums := add_le_add (mul_le_mul operator rawDifference (norm_nonneg _) nonnegative)
      (mul_le_mul operators rawAbsolute (norm_nonneg _) (by positivity))
    have estimate : ‖circleBasedProjectedExteriorSeries phase initialCoefficient first -
        circleBasedProjectedExteriorSeries phase finalCoefficient final‖ ≤
      constant * (2 * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) * ‖first - final‖ +
        (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖)) +
      (constant * ‖first - final‖) * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖) := by
      change ‖circleBasedCentroidProjection first firstRaw - circleBasedCentroidProjection final finalRaw‖ ≤ _
      with_reducible_and_instances
        exact le_trans vector sums
    apply estimate.trans
    have finalWeight : 0 ≤ ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖ :=
      tsum_nonneg (fun degree => by positivity)
    have differenceWeight : 0 ≤ ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖ :=
      tsum_nonneg (fun degree => by positivity)
    nlinarith [mul_nonneg nonnegative (mul_nonneg finalWeight (norm_nonneg (first - final))),
      mul_nonneg nonnegative differenceWeight]

end EulerNonuniqueness.Paper
