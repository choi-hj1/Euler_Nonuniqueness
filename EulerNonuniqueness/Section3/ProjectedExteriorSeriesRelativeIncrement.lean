import EulerNonuniqueness.Section3.ProjectedExteriorSeriesTaylor
import EulerNonuniqueness.Section3.ExteriorSeriesCoefficientDifference
import EulerNonuniqueness.General.UniformFirstJetRelativeIncrement

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace
  gaugeOperatorUniformSecondGroup

theorem circleBasedProjectedExteriorSeries_sub_coefficient (phase : Circle)
    (initial final : ℕ → ℂ) (increment : PeriodicC1HolderHalf)
    (bound : ‖standardCircleBanach + increment‖ ≤ 3)
    (initialSummable : Summable (fun degree => (24 : ℝ) ^ (degree + 1) * ‖initial degree‖))
    (finalSummable : Summable (fun degree => (24 : ℝ) ^ (degree + 1) * ‖final degree‖)) :
    circleBasedProjectedExteriorSeries phase initial increment - circleBasedProjectedExteriorSeries phase final increment =
      circleBasedProjectedExteriorSeries phase (fun degree => initial degree - final degree) increment := by
  have raw := exteriorContourPowerSeries_sub_coefficient phase (standardCircleBanach + increment) bound
    initial final initialSummable finalSummable
  have mapped := (circleBasedCentroidProjection increment).map_sub
    (exteriorContourPowerSeries phase initial (standardCircleBanach + increment))
    (exteriorContourPowerSeries phase final (standardCircleBanach + increment))
  unfold circleBasedProjectedExteriorSeries
  exact mapped.symm.trans (congrArg (circleBasedCentroidProjection increment) raw)

theorem circleBasedProjectedExteriorSeries_exists_relative_increment_ball :
    ∃ radius > 0, radius ≤ 1 / 6 ∧ ∃ constant ≥ 0,
      ∀ (phase : Circle) (coefficient : ℕ → ℂ),
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖) →
      ∀ first final initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖first‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖final‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖(circleBasedProjectedExteriorSeries phase coefficient (first + initialIncrement) -
          circleBasedProjectedExteriorSeries phase coefficient first) -
        (circleBasedProjectedExteriorSeries phase coefficient (final + finalIncrement) -
          circleBasedProjectedExteriorSeries phase coefficient final)‖ ≤
        constant * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖) *
          (‖initialIncrement - finalIncrement‖ + ‖first - final‖ * ‖finalIncrement‖) := by
  obtain ⟨outerRadius, positive, smallRadius, constant, one, bounds⟩ :=
    circleBasedProjectedExteriorSeries_exists_uniform_firstJet
  have nonnegative : 0 ≤ constant := le_trans (by norm_num) one
  have radiusLe : outerRadius / 8 ≤ outerRadius := by linarith
  refine ⟨outerRadius / 8, by positivity, radiusLe.trans smallRadius, 6 * constant, by positivity, ?_⟩
  intro phase coefficient weighted first final initialIncrement finalIncrement firstInside finalInside
  obtain ⟨linearBound, taylor, actual⟩ := bounds phase coefficient weighted
  have weightNonnegative : 0 ≤ ∑' degree, (96 : ℝ) ^ (degree + 1) * ‖coefficient degree‖ :=
    tsum_nonneg (fun degree => by positivity)
  have estimate := EulerNonuniqueness.General.relative_increment_of_uniform_first_jet
    (circleBasedProjectedExteriorSeries phase coefficient)
    (circleBasedProjectedExteriorSeriesFirstJet phase coefficient) positive
    (mul_nonneg nonnegative weightNonnegative) linearBound
    (fun point increment inside => by
      simpa only [EulerNonuniqueness.General.linearJetTaylorError] using taylor point increment inside)
    actual first final initialIncrement finalIncrement firstInside finalInside
  exact estimate.trans_eq (by ring)

theorem circleBasedProjectedExteriorSeries_exists_pair_relative_increment_ball :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ (phase : Circle) (initialCoefficient finalCoefficient : ℕ → ℂ),
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) →
      Summable (fun degree => (96 : ℝ) ^ (degree + 1) * ‖finalCoefficient degree‖) →
      ∀ first final initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖first‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖final‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖(circleBasedProjectedExteriorSeries phase initialCoefficient (first + initialIncrement) -
          circleBasedProjectedExteriorSeries phase initialCoefficient first) -
        (circleBasedProjectedExteriorSeries phase finalCoefficient (final + finalIncrement) -
          circleBasedProjectedExteriorSeries phase finalCoefficient final)‖ ≤ constant *
        ((∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree‖) *
          (‖initialIncrement - finalIncrement‖ + ‖first - final‖ * ‖finalIncrement‖) +
          (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖) *
            ‖finalIncrement‖) := by
  obtain ⟨radius, positive, smallRadius, constant, nonnegative, bound⟩ :=
    circleBasedProjectedExteriorSeries_exists_relative_increment_ball
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro phase initialCoefficient finalCoefficient initialSummable finalSummable first final initialIncrement finalIncrement
    firstInside finalInside
  have differenceSummable := summable_exterior_coefficient_difference_weight initialCoefficient finalCoefficient
    (by norm_num : (0 : ℝ) ≤ 96) initialSummable finalSummable
  have initialTwentyFour := summable_exteriorCoefficientWeight_mono initialCoefficient
    (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 96) initialSummable
  have finalTwentyFour := summable_exteriorCoefficientWeight_mono finalCoefficient
    (by norm_num : (0 : ℝ) ≤ 24) (by norm_num : (24 : ℝ) ≤ 96) finalSummable
  have state := bound phase initialCoefficient initialSummable first final initialIncrement finalIncrement firstInside finalInside
  have finalOnly : ‖final‖ + (‖finalIncrement‖ + ‖(0 : PeriodicC1HolderHalf)‖) ≤ radius := by
    simp only [norm_zero, add_zero]
    linarith [norm_nonneg initialIncrement]
  have coefficient := bound phase (fun degree => initialCoefficient degree - finalCoefficient degree) differenceSummable
    final final finalIncrement 0 finalOnly finalOnly
  simp only [add_zero, sub_self, sub_zero, norm_zero, mul_zero, add_zero] at coefficient
  have shapeBound (increment : PeriodicC1HolderHalf) (inside : ‖increment‖ ≤ radius) :
      ‖standardCircleBanach + increment‖ ≤ 3 :=
    (norm_add_le _ _).trans (by linarith [standardCircleBanach_norm_bound])
  have finalBaseBound : ‖final‖ ≤ radius := by linarith [norm_nonneg initialIncrement, norm_nonneg finalIncrement]
  have shiftedBound : ‖final + finalIncrement‖ ≤ radius :=
    (norm_add_le _ _).trans (by linarith [norm_nonneg initialIncrement])
  have firstIdentity := circleBasedProjectedExteriorSeries_sub_coefficient phase initialCoefficient finalCoefficient
    (final + finalIncrement) (shapeBound _ shiftedBound) initialTwentyFour finalTwentyFour
  have finalIdentity := circleBasedProjectedExteriorSeries_sub_coefficient phase initialCoefficient finalCoefficient
    final (shapeBound _ finalBaseBound) initialTwentyFour finalTwentyFour
  have coefficientIdentity :
      (circleBasedProjectedExteriorSeries phase initialCoefficient (final + finalIncrement) -
        circleBasedProjectedExteriorSeries phase initialCoefficient final) -
      (circleBasedProjectedExteriorSeries phase finalCoefficient (final + finalIncrement) -
        circleBasedProjectedExteriorSeries phase finalCoefficient final) =
      circleBasedProjectedExteriorSeries phase (fun degree => initialCoefficient degree - finalCoefficient degree)
        (final + finalIncrement) -
      circleBasedProjectedExteriorSeries phase (fun degree => initialCoefficient degree - finalCoefficient degree) final := by
    rw [← firstIdentity, ← finalIdentity]
    abel
  have coefficientBound :
      ‖(circleBasedProjectedExteriorSeries phase initialCoefficient (final + finalIncrement) -
        circleBasedProjectedExteriorSeries phase initialCoefficient final) -
      (circleBasedProjectedExteriorSeries phase finalCoefficient (final + finalIncrement) -
        circleBasedProjectedExteriorSeries phase finalCoefficient final)‖ ≤
      constant * (∑' degree, (96 : ℝ) ^ (degree + 1) * ‖initialCoefficient degree - finalCoefficient degree‖) *
        ‖finalIncrement‖ := by rw [coefficientIdentity]; exact coefficient
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (circleBasedProjectedExteriorSeries phase initialCoefficient (first + initialIncrement) -
      circleBasedProjectedExteriorSeries phase initialCoefficient first)
    (circleBasedProjectedExteriorSeries phase initialCoefficient (final + finalIncrement) -
      circleBasedProjectedExteriorSeries phase initialCoefficient final)
    (circleBasedProjectedExteriorSeries phase finalCoefficient (final + finalIncrement) -
      circleBasedProjectedExteriorSeries phase finalCoefficient final)
  exact (triangle.trans (add_le_add state coefficientBound)).trans_eq (by ring)

end EulerNonuniqueness.Paper
