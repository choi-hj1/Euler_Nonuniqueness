import EulerNonuniqueness.Section3.DiskSpectralRelativePhysicalSelf
import EulerNonuniqueness.General.BilinearDiagonalDifference

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance relativeNeutralC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralNeutralField_eq_quadratic_add_remainder (state : PeriodicC1HolderHalf) :
    let transverse := diskPhysicalTransverseProjection (state - diskRelabelNeutralCLM state)
    diskRelabelNeutralCLM (diskSpectralTubularEulerField state) =
      diskRelabelNeutralCLM (diskSpectralFiberQuadraticBilinear state transverse transverse) +
        diskRelabelNeutralCLM (diskSpectralTubularPhysicalCubicRemainder state) := by
  dsimp only
  have identity : diskRelabelNeutralCLM (diskSpectralTubularPhysicalCubicRemainder state) =
      diskRelabelNeutralCLM (diskSpectralTubularEulerField state) -
        diskRelabelNeutralCLM (diskSpectralFiberQuadraticBilinear state
          (diskPhysicalTransverseProjection (state - diskRelabelNeutralCLM state))
          (diskPhysicalTransverseProjection (state - diskRelabelNeutralCLM state))) := by
    simp only [diskSpectralTubularPhysicalCubicRemainder, map_sub,
      diskRelabelNeutralCLM_rotatingDerivative_zero, sub_zero]
  rw [identity]
  abel

theorem diskSpectralNeutralField_difference_norm_le (initial final : PeriodicC1HolderHalf) :
    let first := diskPhysicalTransverseProjection (initial - diskRelabelNeutralCLM initial)
    let second := diskPhysicalTransverseProjection (final - diskRelabelNeutralCLM final)
    ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField initial) -
      diskRelabelNeutralCLM (diskSpectralTubularEulerField final)‖ ≤
      ‖diskRelabelNeutralCLM‖ *
        (‖diskSpectralFiberQuadraticBilinear initial‖ * (‖first‖ + ‖second‖) * ‖first - second‖ +
          ‖diskSpectralFiberQuadraticBilinear initial - diskSpectralFiberQuadraticBilinear final‖ * ‖second‖ ^ 2 +
          ‖diskSpectralTubularPhysicalCubicRemainder initial -
            diskSpectralTubularPhysicalCubicRemainder final‖) := by
  dsimp only
  rw [diskSpectralNeutralField_eq_quadratic_add_remainder initial,
    diskSpectralNeutralField_eq_quadratic_add_remainder final]
  have identity (first second firstError secondError : PeriodicC1HolderHalf) :
      (diskRelabelNeutralCLM first + diskRelabelNeutralCLM firstError) -
        (diskRelabelNeutralCLM second + diskRelabelNeutralCLM secondError) =
      diskRelabelNeutralCLM ((first - second) + (firstError - secondError)) := by
    simp only [map_add, map_sub]
    abel
  rw [identity]
  apply (diskRelabelNeutralCLM.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add
    (EulerNonuniqueness.General.norm_bilinear_diagonal_difference_le _ _ _ _) le_rfl)

end

end EulerNonuniqueness.Paper
