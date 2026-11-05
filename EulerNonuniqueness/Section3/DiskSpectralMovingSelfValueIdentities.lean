import EulerNonuniqueness.Section3.DiskSpectralMovingSelfDecomposition
import EulerNonuniqueness.Section3.DiskSpectralMovingTransverseCubic
import EulerNonuniqueness.Section3.DiskSpectralMovingNeutralCubic
import EulerNonuniqueness.General.FrozenQuadraticValueDecomposition

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance movingSelfValueC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralTransverseNonlinearField_eq_projectedQuadratic (state : PeriodicC1HolderHalf) :
    diskSpectralTransverseNonlinearField state =
      diskSpectralProjectedQuadratic state (diskPhysicalTransverseProjection state)
        (diskPhysicalTransverseProjection state) +
      diskPhysicalTransverseProjection (diskSpectralTubularPhysicalCubicRemainder state) := by
  have diagonal := diskSpectralProjectedQuadratic_diagonal state
  exact (diskSpectralTransverseNonlinearField_eq_quadratic_add_remainder state).trans
    (congrArg (fun output : PeriodicC1HolderHalf => output +
      diskPhysicalTransverseProjection (diskSpectralTubularPhysicalCubicRemainder state)) diagonal.symm)

theorem diskSpectralFrozenQuadraticVelocity_eq_generator_sub_movingCorrection (state : PeriodicC1HolderHalf) :
    diskSpectralFrozenQuadraticVelocity state 0 =
      diskRotatingDerivative (EulerNonuniqueness.General.quadraticCoordinate
        (diskSpectralMovingQuadraticCorrection state) 1 (diskPhysicalTransverseProjection state)) +
      (diskPhysicalTransverseProjection (diskSpectralTubularPhysicalCubicRemainder state) -
        diskSpectralMovingTransverseCorrection state) := by
  have diagonal := diskSpectralProjectedQuadratic_diagonal state
  have projected := diskSpectralTransverseField_eq_quadratic_add_remainder state
  dsimp only at projected
  have projectedEquation := projected.trans (congrArg
    (fun output : PeriodicC1HolderHalf => diskRotatingDerivative (diskPhysicalTransverseProjection state) + output +
      diskPhysicalTransverseProjection (diskSpectralTubularPhysicalCubicRemainder state)) diagonal.symm)
  have velocityEquation := diskSpectralTransverseNonlinearField_eq_projectedQuadratic state
  unfold diskSpectralFrozenQuadraticVelocity diskSpectralMovingTransverseCorrection
  with_reducible_and_instances
    exact EulerNonuniqueness.General.frozenProjectedQuadraticVelocity_self_decomposition
      diskPhysicalTransverseProjection diskRotatingDerivative diskSpectralProjectedQuadratic
      diskSpectralMovingQuadraticCorrection diskSpectralTubularEulerField state
      (diskSpectralTubularPhysicalCubicRemainder state) (diskSpectralTransverseNonlinearField state)
      (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state))
      projectedEquation velocityEquation (diskSpectralMovingQuadraticCorrection_neutral_parameter state)

theorem diskSpectralMovingSelfVelocity_eq_frozen_sub_neutral (state : PeriodicC1HolderHalf) :
    diskSpectralMovingQuadraticSelfVelocity state =
      diskSpectralFrozenQuadraticVelocity state 0 - diskSpectralMovingNeutralCorrection state := by
  unfold diskSpectralMovingQuadraticSelfVelocity diskSpectralMovingNeutralCorrection
  with_reducible_and_instances rfl

end

end EulerNonuniqueness.Paper
