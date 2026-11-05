import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticSplit
import EulerNonuniqueness.General.MovingQuadraticScaledFamily

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance scaledMovingQuadraticC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralScaledMovingQuadraticCoordinate_eventually_hasDerivAt (frequency : ℝ) :
    ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
    ∀ (trajectory : ℝ → PeriodicC1HolderHalf) (time : ℝ) (forcing : PeriodicC1HolderHalf),
    trajectory time = state →
    HasDerivAt trajectory (frequency • diskSpectralTubularEulerField state + forcing) time →
    HasDerivAt (fun current =>
      let value := diskPhysicalTransverseProjection (trajectory current)
      value - diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (trajectory current)) value value)
      (frequency • diskSpectralMovingQuadraticSelfVelocity state +
        diskSpectralMovingQuadraticForcing state forcing) time := by
  have regular := diskSpectralMovingQuadraticCorrection_hasLipschitzDerivativeNear.1
  unfold diskSpectralMovingQuadraticSelfVelocity diskSpectralMovingQuadraticForcing
    diskSpectralFrozenQuadraticVelocity
  with_reducible_and_instances
    exact EulerNonuniqueness.General.moving_projected_quadratic_scaled_eventually_hasDerivAt
      (Space := PeriodicC1HolderHalf) diskPhysicalTransverseProjection diskRelabelNeutralCLM
      diskRotatingDerivative diskSpectralProjectedQuadratic diskSpectralMovingQuadraticCorrection
      diskSpectralTubularEulerField diskSpectralMovingQuadraticCorrection_homological
      diskSpectralMovingQuadraticCorrection_neutral_parameter regular frequency

end

end EulerNonuniqueness.Paper
