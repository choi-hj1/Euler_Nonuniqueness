import EulerNonuniqueness.Section3.DiskRelabelNeutralPart
import EulerNonuniqueness.Section3.DiskStationaryManifold

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance neutralIdentificationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

local instance neutralIdentificationC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def diskMaterialNeutralEmbeddingCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (c1ProductCLM standardCircleBanach).comp (c1ProductCLM (c1Constant Complex.I))

theorem diskRelabelNeutralCLM_eq_material_embedding :
    diskRelabelNeutralCLM = diskMaterialNeutralEmbeddingCLM.comp diskNeutralCLM := by
  apply ContinuousLinearMap.ext
  intro state
  rfl

theorem diskNeutralCLM_relabel_projection (state : PeriodicC1HolderHalf) :
    diskNeutralCLM (diskRelabelNeutralCLM state) = diskNeutralCLM state := by
  rw [diskRelabelNeutralCLM_apply]
  have actual := diskNeutralCLM_material_constant 0 (diskNeutralCLM state) (diskNeutralCLM_real state)
  have zeroConstant : c1Constant (0 : ℂ) = (0 : PeriodicC1HolderHalf) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl
  simpa only [Complex.ofReal_zero, zeroConstant] using actual

theorem diskRelabelNeutralCLM_difference_norm_le (initial final : PeriodicC1HolderHalf) :
    ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖ ≤
      ‖diskMaterialNeutralEmbeddingCLM‖ * ‖diskNeutralCLM initial - diskNeutralCLM final‖ := by
  have identity : diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final =
      diskMaterialNeutralEmbeddingCLM (diskNeutralCLM initial - diskNeutralCLM final) := by
    rw [diskRelabelNeutralCLM_eq_material_embedding]
    simp only [ContinuousLinearMap.comp_apply, map_sub]
  rw [identity]
  exact diskMaterialNeutralEmbeddingCLM.le_opNorm _

theorem diskNeutralCLM_difference_norm_le (initial final : PeriodicC1HolderHalf) :
    ‖diskNeutralCLM initial - diskNeutralCLM final‖ ≤
      ‖diskNeutralCLM‖ * ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖ := by
  have identity : diskNeutralCLM initial - diskNeutralCLM final =
      diskNeutralCLM (diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final) := by
    rw [map_sub, diskNeutralCLM_relabel_projection, diskNeutralCLM_relabel_projection]
  rw [identity]
  exact diskNeutralCLM.le_opNorm _

end EulerNonuniqueness.Paper
