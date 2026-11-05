import EulerNonuniqueness.Section3.DiskSpectralRelativeTransverseUniform
import EulerNonuniqueness.Section3.DiskSpectralSelfBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

local instance transverseVelocityBoundsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralTransverseNonlinearField_exists_eventual_quadratic_bound :
    ∃ constant ≥ 0, ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
      diskSpectralTubularArea state = Real.pi →
      ‖diskSpectralTransverseNonlinearField state‖ ≤ constant * ‖diskPhysicalTransverseProjection state‖ ^ 2 := by
  obtain ⟨radius, positive, remainderConstant, remainderNonnegative, bilinearConstant, bilinearNonnegative,
      correctionConstant, correctionNonnegative, neutralConstant, neutralNonnegative, bounds⟩ :=
    diskSpectral_exists_uniform_projected_self_bounds
  refine ⟨remainderConstant + ‖diskPhysicalTransverseProjection‖ ^ 3 * bilinearConstant, by positivity, ?_⟩
  let relative : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    ContinuousLinearMap.id ℝ PeriodicC1HolderHalf - diskRelabelNeutralCLM
  have sizeContinuous : ContinuousAt (fun state => ‖diskRelabelNeutralCLM state‖ + ‖relative state‖)
      (0 : PeriodicC1HolderHalf) :=
    diskRelabelNeutralCLM.continuous.continuousAt.norm.add relative.continuous.continuousAt.norm
  have small : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskRelabelNeutralCLM state‖ + ‖relative state‖ < radius :=
    sizeContinuous.eventually (gt_mem_nhds (by simpa only [map_zero, norm_zero, zero_add] using positive))
  have transverseSmall : ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf), ‖diskPhysicalTransverseProjection state‖ < 1 :=
    diskPhysicalTransverseProjection.continuous.continuousAt.norm.eventually
      (gt_mem_nhds (by simp only [map_zero, norm_zero]; norm_num))
  filter_upwards [small, transverseSmall] with state inside transverseSmall area
  have stateBounds := bounds state inside.le area
  have bilinearBound : ‖diskSpectralProjectedQuadratic state‖ ≤
      ‖diskPhysicalTransverseProjection‖ ^ 3 * bilinearConstant :=
    (diskSpectralProjectedQuadratic_norm_le state).trans
      (mul_le_mul_of_nonneg_left stateBounds.2.1 (by positivity))
  have quadraticBound : ‖diskSpectralProjectedQuadratic state (diskPhysicalTransverseProjection state)
      (diskPhysicalTransverseProjection state)‖ ≤
      (‖diskPhysicalTransverseProjection‖ ^ 3 * bilinearConstant) * ‖diskPhysicalTransverseProjection state‖ ^ 2 := by
    calc
      _ ≤ ‖diskSpectralProjectedQuadratic state (diskPhysicalTransverseProjection state)‖ *
          ‖diskPhysicalTransverseProjection state‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖diskSpectralProjectedQuadratic state‖ * ‖diskPhysicalTransverseProjection state‖) *
          ‖diskPhysicalTransverseProjection state‖ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖diskPhysicalTransverseProjection‖ ^ 3 * bilinearConstant) * ‖diskPhysicalTransverseProjection state‖ ^ 2 := by
        rw [pow_two, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right bilinearBound (norm_nonneg _)) (norm_nonneg _)
  have identity : diskSpectralTransverseNonlinearField state = diskSpectralProjectedRemainder state +
      diskSpectralProjectedQuadratic state (diskPhysicalTransverseProjection state) (diskPhysicalTransverseProjection state) := by
    unfold diskSpectralTransverseNonlinearField diskSpectralProjectedRemainder
    abel
  rw [identity]
  calc
    _ ≤ ‖diskSpectralProjectedRemainder state‖ +
        ‖diskSpectralProjectedQuadratic state (diskPhysicalTransverseProjection state)
          (diskPhysicalTransverseProjection state)‖ := norm_add_le _ _
    _ ≤ remainderConstant * ‖diskPhysicalTransverseProjection state‖ ^ 3 +
        (‖diskPhysicalTransverseProjection‖ ^ 3 * bilinearConstant) * ‖diskPhysicalTransverseProjection state‖ ^ 2 :=
      add_le_add stateBounds.1 quadraticBound
    _ ≤ _ := by
      rw [add_mul]
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ remainderNonnegative
      nlinarith [mul_nonneg (sq_nonneg ‖diskPhysicalTransverseProjection state‖)
        (sub_nonneg.mpr transverseSmall.le)]

end EulerNonuniqueness.Paper
