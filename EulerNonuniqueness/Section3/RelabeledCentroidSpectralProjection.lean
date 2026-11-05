import EulerNonuniqueness.Section3.ContourCentroidSpectralProjection
import EulerNonuniqueness.Section3.FixedRelabelCentroidProjection
import EulerNonuniqueness.Section3.RelabeledForcingValueEquation
import EulerNonuniqueness.General.LinearConjugateCommutation

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] centroidSpectralProjectionC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem contourCentroidGaugeProjection_relabeled_circle_commutes (angular : PeriodicC1HolderHalf)
    (smallAngular : ‖angular‖ < 1 / 2)
    (smallImage : ‖fixedRelabelEquivalence angular smallAngular standardCircleBanach - standardCircleBanach‖ <
      min (1 / 3) (min 1 (2 / (3 * Real.pi)))) :
    (contourCentroidGaugeProjection (fixedRelabelEquivalence angular smallAngular standardCircleBanach)).comp
        (fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular smallAngular standardCircleBanach)) =
      (fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular smallAngular standardCircleBanach)).comp
        (contourCentroidGaugeProjection (fixedRelabelEquivalence angular smallAngular standardCircleBanach)) := by
  have circleSmall : ‖standardCircleBanach - standardCircleBanach‖ < min (1 / 3) (min 1 (2 / (3 * Real.pi))) := by
    rw [sub_self, norm_zero]
    positivity
  have fieldIdentity := diskEulerRotatingField_derivative_fixedRelabel angular smallAngular standardCircleBanach
    (lt_min_iff.mp circleSmall).2 (lt_min_iff.mp smallImage).2
  rw [diskEulerRotatingField_hasFDerivAt_circle.fderiv] at fieldIdentity
  have projectionIdentity :
      (contourCentroidGaugeProjection (fixedRelabelEquivalence angular smallAngular standardCircleBanach)).comp
          (fixedRelabelEquivalence angular smallAngular).toContinuousLinearMap =
        (fixedRelabelEquivalence angular smallAngular).toContinuousLinearMap.comp
          (contourCentroidGaugeProjection standardCircleBanach) := by
    apply ContinuousLinearMap.ext
    intro direction
    exact contourCentroidGaugeProjection_fixedRelabel angular smallAngular standardCircleBanach direction
      (lt_min_iff.mp circleSmall).1 (lt_min_iff.mp smallImage).1
  exact EulerNonuniqueness.General.commute_of_linear_conjugate (fixedRelabelEquivalence angular smallAngular)
    diskRotatingDerivative (contourCentroidGaugeProjection standardCircleBanach)
    (fderiv ℝ diskEulerRotatingField (fixedRelabelEquivalence angular smallAngular standardCircleBanach))
    (contourCentroidGaugeProjection (fixedRelabelEquivalence angular smallAngular standardCircleBanach))
    fieldIdentity projectionIdentity contourCentroidGaugeProjection_circle_commutes

end EulerNonuniqueness.Paper
