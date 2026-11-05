import EulerNonuniqueness.Section3.ContourGaugeOperatorUniform
import EulerNonuniqueness.Section3.ExteriorPowerSeriesBounds
import EulerNonuniqueness.General.OperatorFieldFirstJetRemainder

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace
  gaugeOperatorUniformSecondGroup

def circleBasedProjectedExteriorSeries (phase : Circle) (coefficient : ℕ → ℂ)
    (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  circleBasedCentroidProjection increment
    (exteriorContourPowerSeries phase coefficient (standardCircleBanach + increment))

def circleBasedProjectedExteriorSeriesFirstJet (phase : Circle) (coefficient : ℕ → ℂ)
    (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (circleBasedCentroidProjection increment).comp
      (exteriorContourPowerSeriesFirstJet phase coefficient (standardCircleBanach + increment)) +
    (fderiv ℝ circleBasedCentroidProjection increment).flip
      (exteriorContourPowerSeries phase coefficient (standardCircleBanach + increment))

theorem circleBasedProjectedExteriorSeriesFirstJet_apply (phase : Circle) (coefficient : ℕ → ℂ)
    (base increment : PeriodicC1HolderHalf) :
    circleBasedProjectedExteriorSeriesFirstJet phase coefficient base increment =
      circleBasedCentroidProjection base
        (exteriorContourPowerSeriesFirstJet phase coefficient (standardCircleBanach + base) increment) +
      (fderiv ℝ circleBasedCentroidProjection base increment)
        (exteriorContourPowerSeries phase coefficient (standardCircleBanach + base)) := rfl

theorem circleBasedProjectedExteriorSeries_exists_uniform_firstJet :
    ∃ radius > 0, radius ≤ 1 / 6 ∧ ∃ constant ≥ 1,
      ∀ (phase : Circle) (coefficient : ℕ → ℂ),
      Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) →
      (∀ base : PeriodicC1HolderHalf, ‖base‖ ≤ radius →
        ‖circleBasedProjectedExteriorSeriesFirstJet phase coefficient base‖ ≤
          constant * (∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖)) ∧
      (∀ base increment : PeriodicC1HolderHalf, ‖base‖ + ‖increment‖ ≤ radius →
        ‖circleBasedProjectedExteriorSeries phase coefficient (base + increment) -
          circleBasedProjectedExteriorSeries phase coefficient base -
          circleBasedProjectedExteriorSeriesFirstJet phase coefficient base increment‖ ≤
          constant * (∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) * ‖increment‖ ^ 2) ∧
      ∀ base : PeriodicC1HolderHalf, ‖base‖ < radius →
        HasFDerivAt (circleBasedProjectedExteriorSeries phase coefficient)
          (circleBasedProjectedExteriorSeriesFirstJet phase coefficient base) base := by
  obtain ⟨radius, positive, smallRadius, constant, constantOne, operatorBounds, operatorDifference, operatorTaylor⟩ :=
    circleBasedCentroidProjection_exists_uniform_firstJet_bounds
  have constantNonnegative : 0 ≤ constant := by linarith
  have shapeBound (base : PeriodicC1HolderHalf) (bound : ‖base‖ ≤ radius) :
      ‖standardCircleBanach + base‖ ≤ 3 := by
    have triangle := norm_add_le standardCircleBanach base
    linarith [standardCircleBanach_norm_bound]
  refine ⟨radius, positive, smallRadius, 4 * constant, by linarith, ?_⟩
  intro phase coefficient weighted
  have amplitudeNonnegative : 0 ≤ ∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖ :=
    tsum_nonneg (fun power => by positivity)
  have quadratic (base increment : PeriodicC1HolderHalf) (bound : ‖base‖ + ‖increment‖ ≤ radius) :
      ‖circleBasedProjectedExteriorSeries phase coefficient (base + increment) -
          circleBasedProjectedExteriorSeries phase coefficient base -
          circleBasedProjectedExteriorSeriesFirstJet phase coefficient base increment‖ ≤
        (4 * constant) * (∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) * ‖increment‖ ^ 2 := by
    have baseBound : ‖base‖ ≤ radius := by linarith [norm_nonneg increment]
    have finalBound : ‖base + increment‖ ≤ radius := (norm_add_le _ _).trans bound
    have incrementSmall : ‖increment‖ ≤ 1 := by linarith [norm_nonneg base]
    have displacement : (standardCircleBanach + (base + increment)) - (standardCircleBanach + base) = increment := by abel
    have operatorDifferenceBound := operatorDifference (base + increment) base finalBound baseBound
    rw [add_sub_cancel_left] at operatorDifferenceBound
    have valueDifferenceBound := exteriorContourPowerSeries_difference_bound phase coefficient
      (standardCircleBanach + (base + increment)) (standardCircleBanach + base)
      (shapeBound _ finalBound) (shapeBound _ baseBound) (by simpa only [displacement] using incrementSmall) weighted
    rw [displacement] at valueDifferenceBound
    have valueErrorBound := exteriorContourPowerSeriesFirstJet_error_bound phase coefficient
      (standardCircleBanach + (base + increment)) (standardCircleBanach + base)
      (shapeBound _ finalBound) (shapeBound _ baseBound) weighted
    rw [displacement] at valueErrorBound
    have estimate := EulerNonuniqueness.General.operator_field_firstJet_remainder_bound
      (circleBasedCentroidProjection (base + increment)) (circleBasedCentroidProjection base)
      (fderiv ℝ circleBasedCentroidProjection base increment)
      (exteriorContourPowerSeries phase coefficient (standardCircleBanach + (base + increment)))
      (exteriorContourPowerSeries phase coefficient (standardCircleBanach + base))
      (exteriorContourPowerSeriesFirstJet phase coefficient (standardCircleBanach + base) increment)
      constantNonnegative (norm_nonneg increment) amplitudeNonnegative (operatorBounds base baseBound).1
      operatorDifferenceBound (operatorTaylor base increment bound)
      (exteriorContourPowerSeries_norm_bound phase coefficient _ (shapeBound _ baseBound) weighted)
      valueDifferenceBound valueErrorBound
    simpa only [circleBasedProjectedExteriorSeries, circleBasedProjectedExteriorSeriesFirstJet_apply] using estimate
  refine ⟨?_, quadratic, ?_⟩
  · intro base baseBound
    have estimate := EulerNonuniqueness.General.operator_field_firstJet_norm_bound
      (circleBasedCentroidProjection base) (fderiv ℝ circleBasedCentroidProjection base)
      (exteriorContourPowerSeriesFirstJet phase coefficient (standardCircleBanach + base))
      (exteriorContourPowerSeries phase coefficient (standardCircleBanach + base))
      constantNonnegative amplitudeNonnegative (operatorBounds base baseBound).1 (operatorBounds base baseBound).2
      (exteriorContourPowerSeries_norm_bound phase coefficient _ (shapeBound _ baseBound) weighted)
      (exteriorContourPowerSeriesFirstJet_norm_bound96 phase coefficient _ (shapeBound _ baseBound) weighted)
    exact estimate.trans (by nlinarith)
  · intro base baseBound
    apply EulerNonuniqueness.General.hasFDerivAt_of_eventual_quadratic_remainder
      (circleBasedProjectedExteriorSeries phase coefficient) (circleBasedProjectedExteriorSeriesFirstJet phase coefficient base) base
      (constant := (4 * constant) * (∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖)) (by positivity)
    have nearby : ∀ᶠ increment : PeriodicC1HolderHalf in 𝓝 0, ‖base‖ + ‖increment‖ < radius := by
      have continuity : Continuous (fun increment : PeriodicC1HolderHalf => ‖base‖ + ‖increment‖) :=
        continuous_const.add continuous_norm
      exact (continuity.tendsto 0).eventually (eventually_lt_nhds (by simpa only [norm_zero, add_zero] using baseBound))
    filter_upwards [nearby] with increment inside
    exact quadratic base increment inside.le

end EulerNonuniqueness.Paper
