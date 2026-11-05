import EulerNonuniqueness.Section3.CentroidStrainFixedRelabel
import EulerNonuniqueness.Section3.ContourCentroidGauge

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance relabelCentroidProjectionC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace

theorem fixedRelabelEquivalence_constant (angular : PeriodicC1HolderHalf) (small : ‖angular‖ < 1 / 2)
    (value : ℂ) : fixedRelabelEquivalence angular small (c1Constant value) = c1Constant value := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem contourCentroidGaugeProjection_fixedRelabel (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2) (data direction : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (composedSmall : ‖fixedRelabelEquivalence angular angularSmall data - standardCircleBanach‖ < 1 / 3) :
    contourCentroidGaugeProjection (fixedRelabelEquivalence angular angularSmall data)
        (fixedRelabelEquivalence angular angularSmall direction) =
      fixedRelabelEquivalence angular angularSmall (contourCentroidGaugeProjection data direction) := by
  have derivative := congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] ℂ => operator direction)
    (contourCentroidFunctional_derivative_fixedRelabel angular angularSmall data small composedSmall)
  change fderiv ℝ contourCentroidFunctional (fixedRelabelEquivalence angular angularSmall data)
      (fixedRelabelEquivalence angular angularSmall direction) =
    fderiv ℝ contourCentroidFunctional data direction at derivative
  rw [contourCentroidGaugeProjection_apply, contourCentroidGaugeProjection_apply, derivative, map_sub,
    fixedRelabelEquivalence_constant]

end EulerNonuniqueness.Paper
