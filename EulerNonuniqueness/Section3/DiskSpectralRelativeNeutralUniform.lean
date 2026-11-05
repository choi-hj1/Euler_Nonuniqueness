import EulerNonuniqueness.Section3.DiskSpectralRelativeNeutral
import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticLipschitz
import EulerNonuniqueness.General.LocalRelativeQuadraticField

namespace EulerNonuniqueness.Paper

noncomputable section

open Metric

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance relativeNeutralUniformC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralNeutralField_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
    initial ∈ ball 0 radius → final ∈ ball 0 radius →
    diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
    let first := diskPhysicalTransverseProjection (initial - diskRelabelNeutralCLM initial)
    let second := diskPhysicalTransverseProjection (final - diskRelabelNeutralCLM final)
    ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField initial) -
      diskRelabelNeutralCLM (diskSpectralTubularEulerField final)‖ ≤ constant *
      ((‖first‖ + ‖second‖) * ‖first - second‖ +
        (‖first‖ + ‖second‖) ^ 2 * ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
  let transverse : PeriodicC1HolderHalf → PeriodicC1HolderHalf :=
    fun state => diskPhysicalTransverseProjection (state - diskRelabelNeutralCLM state)
  have regular := diskSpectralFiberQuadraticBilinear_lipschitzNear
  have remainder := diskSpectralTubularPhysicalCubicRemainder_exists_relative_physical_ball
  have estimate := diskSpectralNeutralField_difference_norm_le
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_relative_quadratic_field_ball
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM transverse
      diskSpectralFiberQuadraticBilinear
      (fun state => diskRelabelNeutralCLM (diskSpectralTubularEulerField state))
      diskSpectralTubularPhysicalCubicRemainder (fun state => diskSpectralTubularArea state = Real.pi)
      (by fun_prop) (by simp only [transverse, map_zero, sub_self])
      (norm_nonneg diskRelabelNeutralCLM) regular diskSpectralFiberQuadraticBilinear_neutral_parameter
      remainder estimate

end

end EulerNonuniqueness.Paper
