import EulerNonuniqueness.Section3.DiskSpectralPhysicalSelfDecomposition
import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticLipschitz
import EulerNonuniqueness.General.LocalRelativeQuadraticField
import EulerNonuniqueness.General.BilinearDiagonalDifference

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance relativeTransverseUniformC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskSpectralTransverseNonlinearField (state : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskPhysicalTransverseProjection (diskSpectralTubularEulerField state) -
    diskRotatingDerivative (diskPhysicalTransverseProjection state)

theorem diskSpectralTransverseNonlinearField_eq_quadratic_add_remainder (state : PeriodicC1HolderHalf) :
    diskSpectralTransverseNonlinearField state =
      diskPhysicalTransverseProjection (diskSpectralFiberQuadraticBilinear state
        (diskPhysicalTransverseProjection state) (diskPhysicalTransverseProjection state)) +
      diskPhysicalTransverseProjection (diskSpectralTubularPhysicalCubicRemainder state) := by
  unfold diskSpectralTransverseNonlinearField
  rw [diskSpectralTransverseField_eq_quadratic_add_remainder]
  abel

theorem diskSpectralTransverseNonlinearField_difference_norm_le (initial final : PeriodicC1HolderHalf) :
    ‖diskSpectralTransverseNonlinearField initial - diskSpectralTransverseNonlinearField final‖ ≤
      ‖diskPhysicalTransverseProjection‖ *
        (‖diskSpectralFiberQuadraticBilinear initial‖ *
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          ‖diskSpectralFiberQuadraticBilinear initial - diskSpectralFiberQuadraticBilinear final‖ *
            ‖diskPhysicalTransverseProjection final‖ ^ 2 +
          ‖diskSpectralTubularPhysicalCubicRemainder initial - diskSpectralTubularPhysicalCubicRemainder final‖) := by
  rw [diskSpectralTransverseNonlinearField_eq_quadratic_add_remainder initial,
    diskSpectralTransverseNonlinearField_eq_quadratic_add_remainder final]
  have identity (first second firstError secondError : PeriodicC1HolderHalf) :
      (diskPhysicalTransverseProjection first + diskPhysicalTransverseProjection firstError) -
        (diskPhysicalTransverseProjection second + diskPhysicalTransverseProjection secondError) =
      diskPhysicalTransverseProjection ((first - second) + (firstError - secondError)) := by
    simp only [map_add, map_sub]
    abel
  rw [identity]
  apply (diskPhysicalTransverseProjection.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add
    (EulerNonuniqueness.General.norm_bilinear_diagonal_difference_le _ _ _ _) le_rfl)

theorem diskSpectralTransverseNonlinearField_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖diskSpectralTransverseNonlinearField initial - diskSpectralTransverseNonlinearField final‖ ≤ constant *
        ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
            ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
  have regular := diskSpectralFiberQuadraticBilinear_lipschitzNear
  have remainder := diskSpectralTubularPhysicalCubicRemainder_exists_relative_physical_ball
  have remainderLiteral : ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖diskSpectralTubularPhysicalCubicRemainder initial - diskSpectralTubularPhysicalCubicRemainder final‖ ≤ constant *
        ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
            ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 3 *
            ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
    simpa only [diskSpectralPhysicalTransverse_eq_projection] using remainder
  have estimate := diskSpectralTransverseNonlinearField_difference_norm_le
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_relative_quadratic_field_ball
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskPhysicalTransverseProjection
      diskSpectralFiberQuadraticBilinear diskSpectralTransverseNonlinearField
      diskSpectralTubularPhysicalCubicRemainder (fun state => diskSpectralTubularArea state = Real.pi)
      (by fun_prop) (map_zero _) (norm_nonneg diskPhysicalTransverseProjection)
      regular diskSpectralFiberQuadraticBilinear_neutral_parameter remainderLiteral estimate

end EulerNonuniqueness.Paper
