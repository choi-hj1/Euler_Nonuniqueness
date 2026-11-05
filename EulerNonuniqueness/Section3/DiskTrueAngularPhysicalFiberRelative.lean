import EulerNonuniqueness.Section3.DiskPhysicalSpectralRelativeArea
import EulerNonuniqueness.Section3.DiskNeutralIdentification

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskPhysicalSpectralChart_exists_true_angular_relative_defect_ball :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖(diskPhysicalSpectralChart initial - diskRelabelCurve (diskNeutralCLM initial) 1) -
        (diskPhysicalSpectralChart final - diskRelabelCurve (diskNeutralCLM final) 1)‖ ≤ constant *
        (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨radius, positive, constant, nonnegative, relative⟩ :=
    diskPhysicalSpectralDefect_exists_relative_physical_ball
  let enlarged := constant * (1 + ‖diskMaterialNeutralEmbeddingCLM‖) + 1
  have enlargedOne : 1 ≤ enlarged := by
    have productNonnegative : 0 ≤ constant * (1 + ‖diskMaterialNeutralEmbeddingCLM‖) := by positivity
    dsimp only [enlarged]
    linarith
  refine ⟨radius, positive, enlarged, enlargedOne, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea
  have actual := relative initial final initialInside finalInside initialArea finalArea
  have stationary (state : PeriodicC1HolderHalf) :
      diskStationaryChart (diskRelabelNeutralCLM state) = diskRelabelCurve (diskNeutralCLM state) 1 := by
    rw [diskRelabelNeutralCLM_apply, diskStationaryChart_relabel _ (diskNeutralCLM_real state)]
  simp only [diskPhysicalSpectralDefect, stationary] at actual
  have identified := diskRelabelNeutralCLM_difference_norm_le initial final
  have scaled := mul_le_mul_of_nonneg_left identified (by positivity : 0 ≤
    ‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖)
  have bounded := actual.trans (mul_le_mul_of_nonneg_left
    (add_le_add_left scaled ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖) nonnegative)
  apply bounded.trans
  have extra : 0 ≤ constant * ‖diskMaterialNeutralEmbeddingCLM‖ *
      ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
    constant * (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
      ‖diskNeutralCLM initial - diskNeutralCLM final‖ +
    ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
    (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
      ‖diskNeutralCLM initial - diskNeutralCLM final‖ := by positivity
  dsimp only [enlarged]
  nlinarith only [extra]

end EulerNonuniqueness.Paper
