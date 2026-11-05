import EulerNonuniqueness.Section3.DiskSpectralTransverseVelocityBounds
import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticLipschitz
import EulerNonuniqueness.General.LocalQuadraticVelocitySymmetricCubic

namespace EulerNonuniqueness.Paper

noncomputable section

open Metric

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

local instance movingTransverseCubicC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskSpectralMovingTransverseCorrection (state : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
      (diskSpectralTransverseNonlinearField state) (diskPhysicalTransverseProjection state) +
    diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
      (diskPhysicalTransverseProjection state) (diskSpectralTransverseNonlinearField state)

theorem diskSpectralMovingTransverseCorrection_exists_relative_cubic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖diskSpectralMovingTransverseCorrection initial - diskSpectralMovingTransverseCorrection final‖ ≤ constant *
        ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
          ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 3 *
            ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
  have regular := diskSpectralMovingQuadraticCorrection_lipschitzNear
  have relative := diskSpectralTransverseNonlinearField_exists_relative_quadratic_ball
  have absolute := diskSpectralTransverseNonlinearField_exists_eventual_quadratic_bound
  unfold diskSpectralMovingTransverseCorrection
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_relative_quadratic_velocity_symmetric_ball
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM
      (fun state => diskPhysicalTransverseProjection state) diskSpectralTransverseNonlinearField
      diskSpectralMovingQuadraticCorrection (fun state => diskSpectralTubularArea state = Real.pi)
      regular relative absolute

end

end EulerNonuniqueness.Paper
