import EulerNonuniqueness.Section3.DiskPhysicalSpectralLeftInverse
import EulerNonuniqueness.General.LocalLeftInverseDerivative

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralInverseJacobianC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskPhysicalSpectralInverseDerivative_eventually_jacobian_identity :
    ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf),
      ∀ coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
        HasFDerivAt diskPhysicalSpectralChart coordinates.toContinuousLinearMap point →
        diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point) =
          coordinates.symm.toContinuousLinearMap := by
  have chartLimit : Tendsto diskPhysicalSpectralChart (𝓝 (0 : PeriodicC1HolderHalf))
      (𝓝 standardCircleBanach) := by
    simpa only [diskPhysicalSpectralChart_zero] using
      diskPhysicalSpectralChart_hasLipschitzDerivativeNear.lipschitzNear.continuousAt.tendsto
  filter_upwards [diskPhysicalSpectralCoordinate_eventually_left_inverse.eventually_nhds,
    chartLimit.eventually diskPhysicalSpectralCoordinate_eventually_inverse_derivative]
    with point leftInverse inverseDerivative coordinates forwardActual
  have actualInverse := inverseDerivative.2.1
  with_reducible
    exact EulerNonuniqueness.General.derivative_of_local_left_inverse
      diskPhysicalSpectralChart diskPhysicalSpectralCoordinate point coordinates
      (diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point))
      leftInverse forwardActual actualInverse

end EulerNonuniqueness.Paper
