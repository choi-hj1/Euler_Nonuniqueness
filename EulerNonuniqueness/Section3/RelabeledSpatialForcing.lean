import EulerNonuniqueness.Section3.ExteriorGaugeContourSeries
import EulerNonuniqueness.Section3.FixedRelabelCentroidProjection

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance relabeledSpatialC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem SpatialContourField.rawRotatedCompose_fixedRelabel {center : ℂ} {radius : ℝ}
    (source : SpatialContourField center radius) (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) (phase : Circle)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3)
    (composedBound : ‖fixedRelabelEquivalence angular small data‖ ≤ 3) :
    source.rawRotatedCompose (fixedRelabelEquivalence angular small data) phase radiusPositive composedBound =
      fixedRelabelEquivalence angular small (source.rawRotatedCompose data phase radiusPositive bound) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [source.rawRotatedCompose_value, fixedRelabelEquivalence_value,
    fixedRelabelEquivalence_value, source.rawRotatedCompose_value]

theorem SpatialContourField.gaugeRawRotatedCompose_fixedRelabel {center : ℂ} {radius : ℝ}
    (source : SpatialContourField center radius) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data : PeriodicC1HolderHalf) (phase : Circle)
    (radiusPositive : 0 < radius) (bound : ‖data‖ ≤ 3)
    (composedBound : ‖fixedRelabelEquivalence angular angularSmall data‖ ≤ 3)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ < 1 / 3) :
    contourCentroidGaugeProjection (fixedRelabelEquivalence angular angularSmall data)
        (source.rawRotatedCompose (fixedRelabelEquivalence angular angularSmall data) phase radiusPositive composedBound) =
      fixedRelabelEquivalence angular angularSmall
        (contourCentroidGaugeProjection data (source.rawRotatedCompose data phase radiusPositive bound)) := by
  rw [source.rawRotatedCompose_fixedRelabel angular angularSmall data phase radiusPositive bound composedBound]
  exact contourCentroidGaugeProjection_fixedRelabel angular angularSmall data _ small composedSmall

theorem areaNormalizedAntiholomorphicForcing_circle (degree : ℕ) :
    areaNormalizedAntiholomorphicForcing degree standardCircleBanach =
      c1Conjugate (c1NaturalPower standardCircleBanach (degree + 1)) := by
  unfold areaNormalizedAntiholomorphicForcing
  rw [contourPolynomialMoment_circle_positive, star_zero, zero_div]
  have constantZero : c1Constant (0 : ℂ) = 0 := c1ConstantCLM.map_zero
  rw [constantZero, sub_zero]

open EulerNonuniqueness.Section6

theorem exterior_gauge_circle_eq_rotatedCompose {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {center : ℂ} {radius distance : ℝ} (source : SpatialContourField center radius)
    (fieldIdentity : source.field = biotSavart vorticity) (phase : Circle)
    (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 24 * radius / distance < 1) :
    contourCentroidGaugeProjection standardCircleBanach
        (source.rawRotatedCompose standardCircleBanach phase radiusPositive
          (standardCircleBanach_norm_bound.trans (by norm_num))) =
      source.rotatedCompose standardCircleBanach phase radiusPositive
        (standardCircleBanach_norm_bound.trans (by norm_num)) := by
  rw [exterior_gauge_contour_series_eq integrable membership source fieldIdentity phase standardCircleBanach
      (standardCircleBanach_norm_bound.trans (by norm_num)) (by simp) radiusPositive positive separated small,
    exterior_general_contour_series_eq integrable membership source fieldIdentity phase standardCircleBanach
      (standardCircleBanach_norm_bound.trans (by norm_num)) radiusPositive positive separated small]
  apply tsum_congr
  intro degree
  rw [areaNormalizedAntiholomorphicForcing_circle]
  rfl

end EulerNonuniqueness.Paper
