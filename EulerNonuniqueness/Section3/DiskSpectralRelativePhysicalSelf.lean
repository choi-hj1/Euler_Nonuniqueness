import EulerNonuniqueness.Section3.DiskSpectralRelativePhysicalCubic
import EulerNonuniqueness.Section3.DiskSpectralRelativeMeanQuadratic

namespace EulerNonuniqueness.Paper

noncomputable section

open Metric

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd chartedBilinearGroup chartedBilinearModule

local instance spectralRelativePhysicalSelfGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskSpectralTubularPhysicalCubicRemainder (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  let relative := increment - diskRelabelNeutralCLM increment
  let transverse := diskPhysicalTransverseProjection relative
  diskSpectralTubularEulerField increment - diskRotatingDerivative relative -
    diskSpectralFiberQuadraticBilinear increment transverse transverse

theorem diskSpectralFiberQuadraticValue_eq_bilinear (increment : PeriodicC1HolderHalf) :
    diskSpectralFiberQuadraticValue increment = diskSpectralFiberQuadraticBilinear increment
      (increment - diskRelabelNeutralCLM increment) (increment - diskRelabelNeutralCLM increment) := by
  have actual := diskSpectralFiberQuadraticBilinear_apply increment
    (increment - diskRelabelNeutralCLM increment) (increment - diskRelabelNeutralCLM increment)
  dsimp only [diskSpectralFiberQuadraticValue]
  with_reducible_and_instances
    exact actual.symm

theorem diskSpectralTubularPhysicalCubicRemainder_eq_sum (increment : PeriodicC1HolderHalf) :
    diskSpectralTubularPhysicalCubicRemainder increment =
      diskSpectralTubularCubicRemainder increment + diskSpectralFiberMeanQuadraticError increment := by
  let relative := increment - diskRelabelNeutralCLM increment
  let transverse := diskPhysicalTransverseProjection relative
  have algebra (velocity linear full projected : PeriodicC1HolderHalf) :
      velocity - linear - projected = (velocity - linear - full) + (full - projected) := by abel
  have first := algebra (diskSpectralTubularEulerField increment) (diskRotatingDerivative relative)
    (diskSpectralFiberQuadraticValue increment) (diskSpectralFiberQuadraticBilinear increment transverse transverse)
  have second := congrArg (fun value : PeriodicC1HolderHalf =>
    (diskSpectralTubularEulerField increment - diskRotatingDerivative relative - diskSpectralFiberQuadraticValue increment) +
      (value - diskSpectralFiberQuadraticBilinear increment transverse transverse))
    (diskSpectralFiberQuadraticValue_eq_bilinear increment)
  dsimp only [diskSpectralTubularPhysicalCubicRemainder, diskSpectralTubularCubicRemainder,
    diskSpectralFiberMeanQuadraticError]
  with_reducible_and_instances
    exact first.trans second

theorem diskSpectralTubularPhysicalCubicRemainder_exists_relative_physical_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      let first := diskPhysicalTransverseProjection (initial - diskRelabelNeutralCLM initial)
      let second := diskPhysicalTransverseProjection (final - diskRelabelNeutralCLM final)
      ‖diskSpectralTubularPhysicalCubicRemainder initial - diskSpectralTubularPhysicalCubicRemainder final‖ ≤ constant *
        ((‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ +
          (‖first‖ + ‖second‖) ^ 3 * ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖) := by
  obtain ⟨rawRadius, rawPositive, rawConstant, rawNonnegative, rawBound⟩ :=
    diskSpectralTubularCubicRemainder_exists_relative_physical_ball
  obtain ⟨meanRadius, meanPositive, meanConstant, meanNonnegative, meanBound⟩ :=
    diskSpectralFiberMeanQuadraticError_exists_relative_physical_ball
  refine ⟨min rawRadius meanRadius, lt_min rawPositive meanPositive,
    rawConstant + meanConstant, add_nonneg rawNonnegative meanNonnegative, ?_⟩
  intro initial final initialInside finalInside initialConstraint finalConstraint
  have initialRaw := Metric.ball_subset_ball (min_le_left rawRadius meanRadius) initialInside
  have finalRaw := Metric.ball_subset_ball (min_le_left rawRadius meanRadius) finalInside
  have initialMean := Metric.ball_subset_ball (min_le_right rawRadius meanRadius) initialInside
  have finalMean := Metric.ball_subset_ball (min_le_right rawRadius meanRadius) finalInside
  have rawEstimate := rawBound initial final initialRaw finalRaw initialConstraint finalConstraint
  have meanEstimate := meanBound initial final initialMean finalMean initialConstraint finalConstraint
  have differenceIdentity :
      diskSpectralTubularPhysicalCubicRemainder initial - diskSpectralTubularPhysicalCubicRemainder final =
      (diskSpectralTubularCubicRemainder initial - diskSpectralTubularCubicRemainder final) +
        (diskSpectralFiberMeanQuadraticError initial - diskSpectralFiberMeanQuadraticError final) := by
    rw [diskSpectralTubularPhysicalCubicRemainder_eq_sum, diskSpectralTubularPhysicalCubicRemainder_eq_sum]
    abel
  rw [differenceIdentity]
  apply (norm_add_le _ _).trans ((add_le_add rawEstimate meanEstimate).trans_eq ?_)
  ring

end

end EulerNonuniqueness.Paper
