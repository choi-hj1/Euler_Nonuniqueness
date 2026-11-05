import EulerNonuniqueness.Section3.DiskSpectralScaledSlope
import EulerNonuniqueness.General.ScalarNormalFormBudget

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

local instance spectralUniformSlopeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralScaledCoordinate_exists_uniform_norm_slope :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {curve : ℝ → PeriodicC1HolderHalf} {time frequency : ℝ} {forcing : PeriodicC1HolderHalf},
      HasDerivAt curve (frequency • diskSpectralTubularEulerField (curve time) + forcing) time →
      ‖diskRelabelNeutralCLM (curve time)‖ + ‖curve time - diskRelabelNeutralCLM (curve time)‖ ≤ radius →
      diskSpectralTubularArea (curve time) = Real.pi →
      ‖diskPhysicalTransverseProjection (curve time)‖ ≤ 1 →
      ∀ threshold : ℝ,
      constant * (|frequency| * ‖diskPhysicalTransverseProjection (curve time)‖ ^ 3 + ‖forcing‖) < threshold →
      ∀ᶠ later in 𝓝[>] time,
        slope (fun current => ‖diskPhysicalScaledGroup frequency (-current)
          (EulerNonuniqueness.General.quadraticCoordinate
            (diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM (curve current))) 1
            (diskPhysicalTransverseProjection (curve current)))‖) time later < threshold := by
  obtain ⟨selfRadius, selfPositive, remainderConstant, remainderNonnegative, bilinearConstant,
    bilinearNonnegative, correctionConstant, correctionNonnegative, neutralConstant, neutralNonnegative, selfBounds⟩ :=
    diskSpectral_exists_uniform_projected_self_bounds
  obtain ⟨lipschitzRadius, lipschitzPositive, lipschitzConstant, lipschitz⟩ :=
    diskSpectralMovingQuadraticCorrection_exists_lipschitz_ball
  let radius := min selfRadius (lipschitzRadius / 2)
  let selfCoefficient := remainderConstant + 2 * correctionConstant *
    (‖diskPhysicalTransverseProjection‖ ^ 3 * bilinearConstant + remainderConstant)
  let forcingCoefficient := (1 + 2 * correctionConstant) * ‖diskPhysicalTransverseProjection‖
  let costSelf := (lipschitzConstant : ℝ) * neutralConstant
  let costForce := (lipschitzConstant : ℝ) * ‖diskRelabelNeutralCLM‖
  let constant := diskPhysicalGroupBound * (selfCoefficient + forcingCoefficient + costSelf + costForce) + 1
  have selfNonnegative : 0 ≤ selfCoefficient := by dsimp [selfCoefficient]; positivity
  have forcingNonnegative : 0 ≤ forcingCoefficient := by dsimp [forcingCoefficient]; positivity
  have costSelfNonnegative : 0 ≤ costSelf := by dsimp [costSelf]; positivity
  have costForceNonnegative : 0 ≤ costForce := by dsimp [costForce]; positivity
  have constantOne : 1 ≤ constant := by
    have positiveProduct : 0 ≤ diskPhysicalGroupBound * (selfCoefficient + forcingCoefficient + costSelf + costForce) :=
      mul_nonneg diskPhysicalGroupBound_nonnegative (by positivity)
    dsimp only [constant]
    linarith
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro curve time frequency forcing equation inside area transverseSmall threshold thresholdStrict
  let transverse := ‖diskPhysicalTransverseProjection (curve time)‖
  let forceSize := ‖forcing‖
  let selfSize := |frequency| * transverse ^ 3
  have transverseNonnegative : 0 ≤ transverse := norm_nonneg _
  have forceNonnegative : 0 ≤ forceSize := norm_nonneg _
  have selfSizeNonnegative : 0 ≤ selfSize := by dsimp [selfSize]; positivity
  have transverseSquare : transverse ^ 2 ≤ 1 := by dsimp only [transverse] at *; nlinarith [sq_nonneg (1 - transverse)]
  have transverseFourth : transverse ^ 4 ≤ transverse ^ 3 := by
    have actual := mul_le_mul_of_nonneg_left transverseSmall (pow_nonneg transverseNonnegative 3)
    dsimp only [transverse] at *
    nlinarith
  obtain ⟨remainderBound, bilinearBound, correctionBound, neutralBound⟩ :=
    selfBounds (curve time) (inside.trans (min_le_left _ _)) area
  have frozenBound := diskSpectralScaledFrozenRemainder_norm_le frequency (curve time) forcing
    remainderNonnegative bilinearNonnegative correctionNonnegative remainderBound bilinearBound correctionBound transverseSmall
  have sourceBound := diskPhysicalTransverseProjection.le_opNorm forcing
  have frozenEstimate : ‖diskSpectralScaledFrozenRemainder frequency (curve time) forcing‖ ≤
      selfCoefficient * selfSize + forcingCoefficient * forceSize := by
    apply frozenBound.trans
    change (|frequency| * selfCoefficient) * transverse ^ 3 +
        (1 + 2 * correctionConstant * transverse) * ‖diskPhysicalTransverseProjection forcing‖ ≤ _
    have scale : 1 + 2 * correctionConstant * transverse ≤ 1 + 2 * correctionConstant := by nlinarith
    have actual := mul_le_mul scale sourceBound (norm_nonneg _) (by positivity : 0 ≤ 1 + 2 * correctionConstant)
    dsimp only [selfSize, forcingCoefficient, forceSize]
    nlinarith
  have neutralEstimate := diskSpectralScaledNeutral_forcing_speed_le frequency (curve time) forcing
    (neutralBound transverseSmall)
  let neutralCost := (lipschitzConstant : ℝ) *
    ‖frequency • diskRelabelNeutralCLM (diskSpectralTubularEulerField (curve time)) + diskRelabelNeutralCLM forcing‖ * transverse ^ 2
  have costEstimate : neutralCost ≤ costSelf * selfSize + costForce * forceSize := by
    have source := diskRelabelNeutralCLM.le_opNorm forcing
    have actual := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (neutralEstimate.trans (add_le_add_left source _)) lipschitzConstant.coe_nonneg)
      (sq_nonneg transverse)
    have fourth := mul_le_mul_of_nonneg_left transverseFourth
      (mul_nonneg lipschitzConstant.coe_nonneg (mul_nonneg (abs_nonneg frequency) neutralNonnegative))
    have square := mul_le_mul_of_nonneg_left transverseSquare
      (mul_nonneg lipschitzConstant.coe_nonneg (mul_nonneg (norm_nonneg diskRelabelNeutralCLM) forceNonnegative))
    dsimp only [neutralCost, costSelf, costForce, selfSize, forceSize] at *
    nlinarith
  let mainSize := ‖diskPhysicalScaledGroup frequency (-time)
    (diskSpectralScaledFrozenRemainder frequency (curve time) forcing)‖
  have mainEstimate : mainSize ≤ diskPhysicalGroupBound * (selfCoefficient * selfSize + forcingCoefficient * forceSize) :=
    (diskPhysicalScaledGroup_norm_bound frequency (-time) _).trans
      (mul_le_mul_of_nonneg_left frozenEstimate diskPhysicalGroupBound_nonnegative)
  have combined : mainSize + diskPhysicalGroupBound * neutralCost < threshold := by
    have actual := add_le_add mainEstimate (mul_le_mul_of_nonneg_left costEstimate diskPhysicalGroupBound_nonnegative)
    have enlarge : diskPhysicalGroupBound * (selfCoefficient * selfSize + forcingCoefficient * forceSize) +
        diskPhysicalGroupBound * (costSelf * selfSize + costForce * forceSize) ≤ constant * (selfSize + forceSize) := by
      rw [show constant = diskPhysicalGroupBound * (selfCoefficient + forcingCoefficient + costSelf + costForce) + 1 from rfl]
      exact EulerNonuniqueness.General.four_coefficient_normal_form_budget
        diskPhysicalGroupBound_nonnegative selfNonnegative forcingNonnegative costSelfNonnegative
        costForceNonnegative selfSizeNonnegative forceNonnegative
    exact (actual.trans enlarge).trans_lt thresholdStrict
  obtain ⟨extra, extraPositive, extraSmall⟩ := exists_pos_mul_lt
    (show 0 < threshold - (mainSize + diskPhysicalGroupBound * neutralCost) by linarith) diskPhysicalGroupBound
  have neutralInside : diskRelabelNeutralCLM (curve time) ∈ ball (0 : PeriodicC1HolderHalf) lipschitzRadius := by
    rw [Metric.mem_ball, dist_zero_right]
    have small := inside.trans (min_le_right _ _)
    linarith [norm_nonneg (curve time - diskRelabelNeutralCLM (curve time))]
  exact diskSpectralScaledCoordinate_eventually_norm_slope_lt frequency isOpen_ball lipschitz equation neutralInside
    (rate := neutralCost + extra) (lt_add_of_pos_right _ extraPositive)
    (EulerNonuniqueness.General.add_mul_lt_of_small_extra extraSmall)

end EulerNonuniqueness.Paper
