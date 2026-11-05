import EulerNonuniqueness.Section3.DiskSpectralRelativeNeutralUniform
import EulerNonuniqueness.Section3.DiskNeutralIdentification
import EulerNonuniqueness.Section3.DiskSpectralProjectedBounds

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskSpectralTrueAngularField_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      ‖diskNeutralCLM (diskSpectralTubularEulerField initial) -
        diskNeutralCLM (diskSpectralTubularEulerField final)‖ ≤ constant *
        ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨radius, positive, constant, nonnegative, relative⟩ :=
    diskSpectralNeutralField_exists_relative_quadratic_ball
  refine ⟨radius, positive, ‖diskNeutralCLM‖ * constant * (1 + ‖diskMaterialNeutralEmbeddingCLM‖),
    by positivity, ?_⟩
  intro initial final initialInside finalInside initialArea finalArea
  have physical := relative initial final initialInside finalInside initialArea finalArea
  simp only [diskSpectralRelative_transverse] at physical
  have angular := (diskNeutralCLM_difference_norm_le
    (diskSpectralTubularEulerField initial) (diskSpectralTubularEulerField final)).trans
      (mul_le_mul_of_nonneg_left physical (norm_nonneg diskNeutralCLM))
  have identified := diskRelabelNeutralCLM_difference_norm_le initial final
  have scalar := mul_le_mul_of_nonneg_left identified (by positivity : 0 ≤
    (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2)
  have budget := add_le_add_left scalar
    ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
      ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖)
  have enlarged :
      (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
          ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
        (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
          (‖diskMaterialNeutralEmbeddingCLM‖ * ‖diskNeutralCLM initial - diskNeutralCLM final‖) ≤
      (1 + ‖diskMaterialNeutralEmbeddingCLM‖) *
        ((‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
            ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
          (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) ^ 2 *
            ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
    nlinarith [mul_nonneg (norm_nonneg diskMaterialNeutralEmbeddingCLM)
      (mul_nonneg (by positivity : 0 ≤ ‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖)
        (norm_nonneg (diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final))),
      mul_nonneg (sq_nonneg (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖))
        (norm_nonneg (diskNeutralCLM initial - diskNeutralCLM final))]
  have scalarBound := mul_le_mul_of_nonneg_left (budget.trans enlarged)
    (by positivity : 0 ≤ ‖diskNeutralCLM‖ * constant)
  exact (angular.trans_eq (by ring)).trans (scalarBound.trans_eq (by ring))

end EulerNonuniqueness.Paper
