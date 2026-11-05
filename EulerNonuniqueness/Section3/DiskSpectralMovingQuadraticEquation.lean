import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticRegularity
import EulerNonuniqueness.Section3.DiskSpectralFrozenQuadraticEquation
import EulerNonuniqueness.Section3.DiskSpectralProjectedTrajectory
import EulerNonuniqueness.General.MovingQuadraticDerivative
import EulerNonuniqueness.General.MovingProjectedQuadraticFamily

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

local instance movingQuadraticEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskSpectralFrozenQuadraticVelocity (state forcing : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.frozenProjectedQuadraticVelocity diskPhysicalTransverseProjection
    diskRotatingDerivative diskSpectralProjectedQuadratic diskSpectralMovingQuadraticCorrection
    diskSpectralTubularEulerField state forcing

theorem diskSpectralMovingQuadraticCoordinate_eventually_hasDerivAt :
    ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
    ∀ (trajectory : ℝ → PeriodicC1HolderHalf) (time : ℝ) (forcing : PeriodicC1HolderHalf),
    trajectory time = state →
    HasDerivAt trajectory (diskSpectralTubularEulerField state + forcing) time →
    HasDerivAt (fun current =>
      let value := diskPhysicalTransverseProjection (trajectory current)
      value - diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (trajectory current)) value value)
      (diskSpectralFrozenQuadraticVelocity state forcing -
        fderiv ℝ diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
          (diskRelabelNeutralCLM (diskSpectralTubularEulerField state + forcing))
          (diskPhysicalTransverseProjection state) (diskPhysicalTransverseProjection state)) time := by
  have regular := diskSpectralMovingQuadraticCorrection_hasLipschitzDerivativeNear.1
  unfold diskSpectralFrozenQuadraticVelocity
  with_reducible_and_instances
    exact EulerNonuniqueness.General.moving_projected_quadratic_family_eventually_hasDerivAt
      (Space := PeriodicC1HolderHalf) diskPhysicalTransverseProjection diskRelabelNeutralCLM
      diskRotatingDerivative diskSpectralProjectedQuadratic diskSpectralMovingQuadraticCorrection
      diskSpectralTubularEulerField diskSpectralMovingQuadraticCorrection_homological
      diskSpectralMovingQuadraticCorrection_neutral_parameter regular

end

end EulerNonuniqueness.Paper
