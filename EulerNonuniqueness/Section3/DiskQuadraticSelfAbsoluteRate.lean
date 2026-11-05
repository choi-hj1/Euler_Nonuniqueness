import EulerNonuniqueness.Section3.DiskSpectralRelativeNormalForm

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete
  EulerNonuniqueness.General.cubicCoefficientEndGroup EulerNonuniqueness.General.cubicCoefficientEndSpace
  EulerNonuniqueness.General.cubicCoefficientBilinearGroup EulerNonuniqueness.General.cubicCoefficientBilinearSpace

local instance quadraticSelfAbsoluteRateC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralMovingSelfRemainder_zero : diskSpectralMovingSelfRemainder 0 = 0 := by
  have fieldZero : diskSpectralTubularEulerField 0 = 0 := by
    simp only [diskSpectralTubularEulerField, diskSpectralTubularChart_zero,
      diskChartedEulerField_zero, map_zero]
  with_reducible_and_instances
    simp only [diskSpectralMovingSelfRemainder, EulerNonuniqueness.General.movingQuadraticSelfRemainder,
      diskSpectralTubularPhysicalCubicRemainder, fieldZero, ContinuousLinearMap.map_zero, sub_zero, add_zero]

theorem diskSpectralMovingSelfRemainder_exists_absolute_cubic_ball :
    ∃ stateRadius > 0, ∃ constant ≥ 1, ∀ state : PeriodicC1HolderHalf,
      state ∈ ball 0 stateRadius → diskSpectralTubularArea state = Real.pi →
      ‖diskSpectralMovingSelfRemainder state‖ ≤ constant * ‖diskPhysicalTransverseProjection state‖ ^ 3 := by
  obtain ⟨relativeRadius, relativePositive, relativeConstant, relativeNonnegative, relatives⟩ :=
    diskSpectralMovingSelfRemainder_exists_relative_cubic_ball
  let stateRadius := min relativeRadius (1 / (1 + ‖diskRelabelNeutralCLM‖))
  let constant := 2 * relativeConstant + 1
  refine ⟨stateRadius, by dsimp only [stateRadius]; positivity, constant, by dsimp only [constant]; linarith, ?_⟩
  intro state inside area
  have stateBound : ‖state‖ ≤ stateRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < stateRadius).le
  have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskRelabelNeutralCLM‖)).mp (stateBound.trans (min_le_right _ _))
  have neutralSmall : ‖diskRelabelNeutralCLM state‖ ≤ 1 := by
    calc
      ‖diskRelabelNeutralCLM state‖ ≤ ‖diskRelabelNeutralCLM‖ * ‖state‖ := diskRelabelNeutralCLM.le_opNorm state
      _ ≤ (1 + ‖diskRelabelNeutralCLM‖) * ‖state‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg state)
      _ = ‖state‖ * (1 + ‖diskRelabelNeutralCLM‖) := mul_comm _ _
      _ ≤ 1 := scaled
  have zeroArea : diskSpectralTubularArea (0 : PeriodicC1HolderHalf) = Real.pi := by
    rw [diskSpectralTubularArea, diskSpectralTubularChart_zero, diskStationaryArea_zero]
  have actual := relatives state 0 (ball_subset_ball (min_le_left _ _) inside)
    (mem_ball_zero_iff.mpr (by simpa using relativePositive)) area zeroArea
  simp only [diskSpectralMovingSelfRemainder_zero, sub_zero, map_zero, norm_zero, add_zero] at actual
  have neutralTerm := mul_le_mul_of_nonneg_left neutralSmall
    (pow_nonneg (norm_nonneg (diskPhysicalTransverseProjection state)) 3)
  have bounded : ‖diskSpectralMovingSelfRemainder state‖ ≤
      relativeConstant * (2 * ‖diskPhysicalTransverseProjection state‖ ^ 3) := by
    apply actual.trans
    apply mul_le_mul_of_nonneg_left _ relativeNonnegative
    nlinarith only [neutralTerm]
  have scalar := mul_le_mul_of_nonneg_right
    (show 2 * relativeConstant ≤ constant by dsimp only [constant]; linarith)
    (pow_nonneg (norm_nonneg (diskPhysicalTransverseProjection state)) 3)
  exact (bounded.trans_eq (by ring)).trans scalar

end EulerNonuniqueness.Paper
