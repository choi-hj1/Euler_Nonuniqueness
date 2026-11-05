import EulerNonuniqueness.Section3.RelabeledSpatialForcing

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance relabeledExteriorGaugeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem diskRelabelCurve_norm_bound_three (angular : PeriodicC1HolderHalf)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3) :
    ‖diskRelabelCurve angular 1‖ ≤ 3 := by
  have triangle := norm_add_le (diskRelabelCurve angular 1 - standardCircleBanach) standardCircleBanach
  rw [sub_add_cancel] at triangle
  linarith [standardCircleBanach_norm_bound]

open EulerNonuniqueness.Section6

theorem exterior_relabeled_gauge_eq_fixedRelabel {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {center : ℂ} {radius distance : ℝ} (source : SpatialContourField center radius)
    (fieldIdentity : source.field = biotSavart vorticity) (phase : Circle)
    (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (nearby : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3)
    (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 24 * radius / distance < 1) :
    contourCentroidGaugeProjection (diskRelabelCurve angular 1)
        (source.rawRotatedCompose (diskRelabelCurve angular 1) phase radiusPositive
          (diskRelabelCurve_norm_bound_three angular nearby)) =
      fixedRelabelEquivalence angular angularSmall
        (source.rotatedCompose standardCircleBanach phase radiusPositive
          (standardCircleBanach_norm_bound.trans (by norm_num))) := by
  have circle := fixedRelabelEquivalence_circle angular angularSmall realValues
  have composedSmall : ‖fixedRelabelEquivalence angular angularSmall standardCircleBanach - standardCircleBanach‖ < 1 / 3 := by
    rw [circle]
    exact nearby
  have composedBound : ‖fixedRelabelEquivalence angular angularSmall standardCircleBanach‖ ≤ 3 := by
    rw [circle]
    exact diskRelabelCurve_norm_bound_three angular nearby
  have covariance := source.gaugeRawRotatedCompose_fixedRelabel angular angularSmall standardCircleBanach phase
    radiusPositive (standardCircleBanach_norm_bound.trans (by norm_num)) composedBound (by simp) composedSmall
  rw [exterior_gauge_circle_eq_rotatedCompose integrable membership source fieldIdentity phase radiusPositive
    positive separated small] at covariance
  simpa only [circle] using covariance

end EulerNonuniqueness.Paper
