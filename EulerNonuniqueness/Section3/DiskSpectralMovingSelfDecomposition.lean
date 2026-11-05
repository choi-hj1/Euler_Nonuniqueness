import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticSplit
import EulerNonuniqueness.Section3.DiskSpectralPhysicalSelfDecomposition
import EulerNonuniqueness.Section3.DiskSpectralRelativeNeutral
import EulerNonuniqueness.General.MovingQuadraticSelfDecomposition

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance movingSelfDecompositionC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskSpectralMovingSelfRemainder (state : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.movingQuadraticSelfRemainder diskPhysicalTransverseProjection
    diskRelabelNeutralCLM diskSpectralProjectedQuadratic diskSpectralMovingQuadraticCorrection
    diskSpectralFiberQuadraticBilinear
    (fderiv ℝ diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state))
    state (diskSpectralTubularPhysicalCubicRemainder state)

theorem diskSpectralMovingQuadraticSelfVelocity_eq_generator_add_remainder (state : PeriodicC1HolderHalf) :
    diskSpectralMovingQuadraticSelfVelocity state =
      diskRotatingDerivative (EulerNonuniqueness.General.quadraticCoordinate
        (diskSpectralMovingQuadraticCorrection state) 1 (diskPhysicalTransverseProjection state)) +
        diskSpectralMovingSelfRemainder state := by
  let differential : PeriodicC1HolderHalf →L[ℝ]
      EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fderiv ℝ diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
  have projected := diskSpectralTransverseField_eq_quadratic_add_remainder state
  have neutral := diskSpectralNeutralField_eq_quadratic_add_remainder state
  dsimp only at projected neutral
  have projectedQuadratic := diskSpectralProjectedQuadratic_diagonal state
  have physicalTransverse := diskSpectralPhysicalTransverse_eq_projection state
  have projectedEquation := projected.trans (congrArg
    (fun value : PeriodicC1HolderHalf => diskRotatingDerivative (diskPhysicalTransverseProjection state) + value +
      diskPhysicalTransverseProjection (diskSpectralTubularPhysicalCubicRemainder state)) projectedQuadratic.symm)
  have neutralEquation := neutral.trans (congrArg
    (fun value : PeriodicC1HolderHalf => diskRelabelNeutralCLM (diskSpectralFiberQuadraticBilinear state value value) +
      diskRelabelNeutralCLM (diskSpectralTubularPhysicalCubicRemainder state)) physicalTransverse)
  unfold diskSpectralMovingQuadraticSelfVelocity diskSpectralFrozenQuadraticVelocity diskSpectralMovingSelfRemainder
  with_reducible_and_instances
    exact EulerNonuniqueness.General.movingQuadraticSelfVelocity_eq_generator_add_remainder
      diskPhysicalTransverseProjection diskRelabelNeutralCLM diskRotatingDerivative
      diskSpectralProjectedQuadratic diskSpectralMovingQuadraticCorrection diskSpectralFiberQuadraticBilinear
      diskSpectralTubularEulerField differential state (diskSpectralTubularPhysicalCubicRemainder state)
      projectedEquation neutralEquation

end

end EulerNonuniqueness.Paper
