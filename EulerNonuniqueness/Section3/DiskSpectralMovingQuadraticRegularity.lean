import EulerNonuniqueness.Section3.DiskSpectralFiberRegularity
import EulerNonuniqueness.General.QuadraticHomologicalLinearMap
import EulerNonuniqueness.General.ProjectedQuadraticLinearMap

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

local instance movingQuadraticRegularityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskSpectralQuadraticHomologicalOperator :
    EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf →L[ℝ]
      EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
  (EulerNonuniqueness.General.quadraticHomologicalLinearMap diskPhysicalGroup diskRotatingDerivative
    (by positivity : 0 < 4 * Real.pi) diskPhysicalGroupBound_nonnegative
    diskPhysicalGroup_zero diskPhysicalGroup_add diskPhysicalGroup_generator diskPhysicalGroup_norm_bound).comp
      (EulerNonuniqueness.General.projectedQuadraticLinearMap diskPhysicalTransverseProjection)

theorem diskSpectralQuadraticHomologicalOperator_apply (parameter : PeriodicC1HolderHalf) :
    diskSpectralQuadraticHomologicalOperator (diskSpectralFiberQuadraticBilinear parameter) =
      diskSpectralMovingQuadraticCorrection parameter := by
  unfold diskSpectralQuadraticHomologicalOperator
  rw [ContinuousLinearMap.comp_apply, EulerNonuniqueness.General.quadraticHomologicalLinearMap_apply,
    EulerNonuniqueness.General.projectedQuadraticLinearMap_apply]
  rfl

theorem diskSpectralMovingQuadraticCorrection_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskSpectralMovingQuadraticCorrection
      (0 : PeriodicC1HolderHalf) := by
  have regular := diskSpectralFiberQuadraticBilinear_hasLipschitzDerivativeNear
  have outer := EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap
    diskSpectralQuadraticHomologicalOperator (diskSpectralFiberQuadraticBilinear 0)
  have composed := outer.comp regular
  simpa only [diskSpectralQuadraticHomologicalOperator_apply] using composed

end

end EulerNonuniqueness.Paper
