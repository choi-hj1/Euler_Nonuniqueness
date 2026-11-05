import EulerNonuniqueness.Section3.DiskSpectralRelativePhysicalSelf
import EulerNonuniqueness.Section3.DiskSpectralProjectionGenerator

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance physicalSelfDecompositionC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralPhysicalTransverse_eq_projection (state : PeriodicC1HolderHalf) :
    diskPhysicalTransverseProjection (state - diskRelabelNeutralCLM state) =
      diskPhysicalTransverseProjection state := by
  rw [map_sub, diskPhysicalTransverseProjection_relabel_zero, sub_zero]

theorem diskSpectralTransverseField_eq_quadratic_add_remainder (state : PeriodicC1HolderHalf) :
    let transverse := diskPhysicalTransverseProjection state
    diskPhysicalTransverseProjection (diskSpectralTubularEulerField state) =
      diskRotatingDerivative transverse +
        diskPhysicalTransverseProjection (diskSpectralFiberQuadraticBilinear state transverse transverse) +
        diskPhysicalTransverseProjection (diskSpectralTubularPhysicalCubicRemainder state) := by
  dsimp only
  have generator : diskRotatingDerivative (state - diskRelabelNeutralCLM state) =
      diskRotatingDerivative (diskPhysicalTransverseProjection state) := by
    rw [map_sub, diskRotatingDerivative_relabel_neutral_zero, sub_zero,
      diskRotatingDerivative_transverse_projection]
  have identity : diskPhysicalTransverseProjection (diskSpectralTubularPhysicalCubicRemainder state) =
      diskPhysicalTransverseProjection (diskSpectralTubularEulerField state) -
        diskRotatingDerivative (diskPhysicalTransverseProjection state) -
        diskPhysicalTransverseProjection (diskSpectralFiberQuadraticBilinear state
          (diskPhysicalTransverseProjection state) (diskPhysicalTransverseProjection state)) := by
    simp only [diskSpectralTubularPhysicalCubicRemainder, map_sub,
      diskPhysicalTransverseProjection_rotatingDerivative, diskSpectralPhysicalTransverse_eq_projection, generator,
      diskPhysicalTransverseProjection_relabel_zero, map_zero, sub_zero]
  rw [identity]
  abel

theorem diskSpectralProjectedQuadratic_diagonal (state : PeriodicC1HolderHalf) :
    let transverse := diskPhysicalTransverseProjection state
    diskSpectralProjectedQuadratic state transverse transverse =
      diskPhysicalTransverseProjection (diskSpectralFiberQuadraticBilinear state transverse transverse) := by
  have idempotent (value : PeriodicC1HolderHalf) :
      diskPhysicalTransverseProjection (diskPhysicalTransverseProjection value) =
        diskPhysicalTransverseProjection value :=
    congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => operator value)
      diskPhysicalTransverseProjection_idempotent
  dsimp only
  unfold diskSpectralProjectedQuadratic EulerNonuniqueness.General.projectedQuadratic
  rw [EulerNonuniqueness.General.bilinearPostcompose_apply]
  simp only [ContinuousLinearMap.bilinearComp_apply, idempotent]

end

end EulerNonuniqueness.Paper
