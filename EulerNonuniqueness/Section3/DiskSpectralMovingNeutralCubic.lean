import EulerNonuniqueness.Section3.DiskSpectralNeutralVelocityBounds
import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticRegularity
import EulerNonuniqueness.Section3.DiskSpectralPhysicalSelfDecomposition
import EulerNonuniqueness.General.LocalMovingQuadraticNeutralCubic

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
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance movingNeutralCubicC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskSpectralMovingNeutralCorrection (state : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  fderiv ℝ diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
    (diskRelabelNeutralCLM (diskSpectralTubularEulerField state))
    (diskPhysicalTransverseProjection state) (diskPhysicalTransverseProjection state)

theorem diskSpectralMovingNeutralCorrection_exists_relative_cubic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖diskSpectralMovingNeutralCorrection initial - diskSpectralMovingNeutralCorrection final‖ ≤ constant *
        ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
          ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 3 *
            ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
  let differential : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ]
      EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fderiv ℝ diskSpectralMovingQuadraticCorrection
  have regular := diskSpectralMovingQuadraticCorrection_hasLipschitzDerivativeNear.2
  have relative := diskSpectralNeutralField_exists_relative_quadratic_ball
  have absolute := diskSpectralNeutralField_exists_eventual_quadratic_bound
  simp only [diskSpectralPhysicalTransverse_eq_projection] at relative
  unfold diskSpectralMovingNeutralCorrection
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_relative_moving_neutral_correction_ball
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM
      (fun state => diskPhysicalTransverseProjection state)
      (fun state => diskRelabelNeutralCLM (diskSpectralTubularEulerField state)) differential
      (fun state => diskSpectralTubularArea state = Real.pi)
      diskPhysicalTransverseProjection.continuous.continuousAt (map_zero _) regular relative absolute

end

end EulerNonuniqueness.Paper
