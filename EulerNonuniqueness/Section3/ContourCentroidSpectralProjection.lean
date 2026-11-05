import EulerNonuniqueness.Section3.ContourCentroidCircleCommutation
import EulerNonuniqueness.Section3.ContourVelocityTranslationDerivative

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance centroidSpectralProjectionC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourCentroidGaugeProjection_circle_commutes :
    (contourCentroidGaugeProjection standardCircleBanach).comp diskRotatingDerivative =
      diskRotatingDerivative.comp (contourCentroidGaugeProjection standardCircleBanach) := by
  apply ContinuousLinearMap.ext
  intro direction
  have intertwines := DFunLike.congr_fun contourCentroidFunctional_circle_derivative_intertwines direction
  have scalarIdentity : (fderiv ℝ contourCentroidFunctional standardCircleBanach) (diskRotatingDerivative direction) =
      (-Complex.I / 2) * (fderiv ℝ contourCentroidFunctional standardCircleBanach) direction := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul] using intertwines
  change contourCentroidGaugeProjection standardCircleBanach (diskRotatingDerivative direction) =
    diskRotatingDerivative (contourCentroidGaugeProjection standardCircleBanach direction)
  rw [contourCentroidGaugeProjection_apply, contourCentroidGaugeProjection_apply, map_sub,
    diskRotatingDerivative_constant, scalarIdentity]

end EulerNonuniqueness.Paper
