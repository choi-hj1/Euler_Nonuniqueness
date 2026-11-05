import EulerNonuniqueness.Section3.CentroidStrainFixedRelabel

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] centroidStrainRelabelC1Group forcingModeC1RealSpace

theorem contourCentroidFunctional_derivative_pullback (angular : PeriodicC1HolderHalf)
    (smallAngular : ‖angular‖ < 1 / 2) (data direction : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (smallImage : ‖fixedRelabelEquivalence angular smallAngular data - standardCircleBanach‖ < 1 / 3) :
    fderiv ℝ contourCentroidFunctional data ((fixedRelabelEquivalence angular smallAngular).symm direction) =
      fderiv ℝ contourCentroidFunctional (fixedRelabelEquivalence angular smallAngular data) direction := by
  have identity := congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] ℂ =>
    operator ((fixedRelabelEquivalence angular smallAngular).symm direction))
    (contourCentroidFunctional_derivative_fixedRelabel angular smallAngular data small smallImage)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using identity.symm

end EulerNonuniqueness.Paper
