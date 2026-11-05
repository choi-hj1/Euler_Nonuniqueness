import EulerNonuniqueness.Section3.DiskTrueAngularPhysicalFiberRelative
import EulerNonuniqueness.Section3.DiskPhysicalSpectralRelabelDefect
import EulerNonuniqueness.Section3.RelabelMapUniformLipschitz

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

local instance trueAngularPhysicalPairBoundsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskPhysicalSpectralChart_exists_true_angular_pair_bounds :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      let firstBase := diskRelabelCurve (diskNeutralCLM initial) 1
      let finalBase := diskRelabelCurve (diskNeutralCLM final) 1
      let firstData := diskPhysicalSpectralChart initial
      let finalData := diskPhysicalSpectralChart final
      ‖firstData - firstBase‖ ≤ constant * ‖diskPhysicalTransverseProjection initial‖ ∧
      ‖finalData - finalBase‖ ≤ constant * ‖diskPhysicalTransverseProjection final‖ ∧
      ‖(firstData - firstBase) - (finalData - finalBase)‖ ≤ constant *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖) ∧
      ‖firstBase - finalBase‖ ≤ constant * ‖diskNeutralCLM initial - diskNeutralCLM final‖ ∧
      ‖firstData - finalData‖ ≤ constant *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨defectRadius, defectPositive, defectConstant, defectOne, defects⟩ :=
    diskPhysicalSpectralChart_exists_uniform_relabel_defect
  obtain ⟨fiberRadius, fiberPositive, fiberConstant, fiberOne, fibers⟩ :=
    diskPhysicalSpectralChart_exists_true_angular_relative_defect_ball
  obtain ⟨baseRadius, basePositive, baseConstant, _, bases⟩ := diskRelabelMap_exists_uniform_lipschitz
  let radius := min fiberRadius (min (defectRadius / (1 + 2 * ‖diskRelabelNeutralCLM‖))
    (min (baseRadius / (1 + ‖diskNeutralCLM‖)) (1 / (2 * (1 + ‖diskPhysicalTransverseProjection‖)))))
  let constant := defectConstant + fiberConstant + (baseConstant : ℝ) + 1
  have defectNonnegative : 0 ≤ defectConstant := by linarith
  have fiberNonnegative : 0 ≤ fiberConstant := by linarith
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith [baseConstant.coe_nonneg]
  have defectLe : defectConstant ≤ constant := by dsimp only [constant]; linarith [baseConstant.coe_nonneg]
  have fiberLe : fiberConstant ≤ constant := by dsimp only [constant]; linarith [baseConstant.coe_nonneg]
  have baseLe : (baseConstant : ℝ) ≤ constant := by dsimp only [constant]; linarith
  have pairLe : fiberConstant + (baseConstant : ℝ) ≤ constant := by dsimp only [constant]; linarith
  refine ⟨radius, by dsimp only [radius]; positivity, constant, constantOne, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea
  dsimp only
  have within {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 radius) :
      state ∈ ball 0 fiberRadius ∧
      ‖diskRelabelNeutralCLM state‖ + ‖state - diskRelabelNeutralCLM state‖ ≤ defectRadius ∧
      ‖diskNeutralCLM state‖ ≤ baseRadius ∧
      ‖diskPhysicalTransverseProjection state‖ ≤ 1 / 2 := by
    have stateSmall : ‖state‖ ≤ radius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < radius).le
    have neutral := diskRelabelNeutralCLM.le_opNorm state
    have angular := diskNeutralCLM.le_opNorm state
    have projected := diskPhysicalTransverseProjection.le_opNorm state
    refine ⟨ball_subset_ball (min_le_left _ _) inside, ?_, ?_, ?_⟩
    · have scaled := (le_div_iff₀ (by positivity : 0 < 1 + 2 * ‖diskRelabelNeutralCLM‖)).mp
        (stateSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
      have relative := norm_sub_le state (diskRelabelNeutralCLM state)
      nlinarith
    · have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskNeutralCLM‖)).mp
        (stateSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
      nlinarith [norm_nonneg state]
    · have scaled := (le_div_iff₀ (by positivity : 0 < 2 * (1 + ‖diskPhysicalTransverseProjection‖))).mp
        (stateSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
      nlinarith [norm_nonneg state]
  have firstWithin := within initialInside
  have finalWithin := within finalInside
  have firstDefect := defects initial firstWithin.2.1 initialArea
  have finalDefect := defects final finalWithin.2.1 finalArea
  have fiber := fibers initial final firstWithin.1 finalWithin.1 initialArea finalArea
  have base := bases (diskNeutralCLM initial) (diskNeutralCLM final) firstWithin.2.2.1 finalWithin.2.2.1
  refine ⟨firstDefect.trans (mul_le_mul_of_nonneg_right defectLe (norm_nonneg _)),
    finalDefect.trans (mul_le_mul_of_nonneg_right defectLe (norm_nonneg _)),
    fiber.trans (mul_le_mul_of_nonneg_right fiberLe (by positivity)),
    base.trans (mul_le_mul_of_nonneg_right baseLe (norm_nonneg _)), ?_⟩
  have projectionSum : ‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖ ≤ 1 := by
    linarith [firstWithin.2.2.2, finalWithin.2.2.2]
  have fiberSimplified := fiber.trans (mul_le_mul_of_nonneg_left
    (add_le_add_left (mul_le_mul_of_nonneg_right projectionSum
      (norm_nonneg (diskNeutralCLM initial - diskNeutralCLM final)))
        ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖) fiberNonnegative)
  simp only [one_mul] at fiberSimplified
  have identity : diskPhysicalSpectralChart initial - diskPhysicalSpectralChart final =
      ((diskPhysicalSpectralChart initial - diskRelabelCurve (diskNeutralCLM initial) 1) -
        (diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1)) +
        (diskRelabelCurve (diskNeutralCLM initial) 1 - diskRelabelCurve (diskNeutralCLM final) 1) := by abel
  have triangle := (norm_add_le _ _).trans (add_le_add fiberSimplified base)
  rw [← identity] at triangle
  have nonnegative : 0 ≤ (baseConstant : ℝ) *
      ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ := by positivity
  have combined : fiberConstant *
      (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
        ‖diskNeutralCLM initial - diskNeutralCLM final‖) +
      (baseConstant : ℝ) * ‖diskNeutralCLM initial - diskNeutralCLM final‖ ≤
      (fiberConstant + (baseConstant : ℝ)) *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by nlinarith only [nonnegative]
  exact (triangle.trans combined).trans (mul_le_mul_of_nonneg_right pairLe (by positivity))

end EulerNonuniqueness.Paper
