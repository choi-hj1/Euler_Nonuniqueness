import EulerNonuniqueness.Section3.DiskPhysicalProjection
import EulerNonuniqueness.General.LinearProjectionSandwich

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalSpectralHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance physicalSpectralC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance physicalSpectralOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem diskPhysicalReconstruction_coordinates :
    diskPhysicalReconstructionCLM.comp diskPhysicalCoordinatesCLM =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  apply ContinuousLinearMap.ext
  intro direction
  change diskPhysicalReconstructionCLM (diskPhysicalCoordinatesCLM direction) = direction
  rw [diskPhysicalReconstructionCLM_apply]
  exact diskPhysicalCoordinates_reconstruct direction

theorem diskPhysicalTransverseProjection_eq_half :
    diskPhysicalTransverseProjection = EulerNonuniqueness.General.negativeInvolutionProjection
      (Space := PeriodicC1HolderHalf) (diskPhysicalGroup (2 * Real.pi)) := by
  unfold diskPhysicalTransverseProjection diskTransverseProjection diskPhysicalGroup
  with_reducible
    exact EulerNonuniqueness.General.negativeInvolutionProjection_sandwich
      (Domain := PeriodicC1HolderHalf) (Middle := DiskLinearState)
      diskPhysicalReconstructionCLM diskPhysicalCoordinatesCLM diskPhysicalReconstruction_coordinates
      (diskLinearGroupOperator (2 * Real.pi))

theorem diskPhysicalGroup_half_square :
    (diskPhysicalGroup (2 * Real.pi)).comp (diskPhysicalGroup (2 * Real.pi)) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  rw [← diskPhysicalGroup_add, show 2 * Real.pi + 2 * Real.pi = 4 * Real.pi by ring]
  simpa only [zero_add, diskPhysicalGroup_zero] using diskPhysicalGroup_period (0 : ℝ)

theorem diskPhysicalTransverseProjection_idempotent :
    diskPhysicalTransverseProjection.comp diskPhysicalTransverseProjection = diskPhysicalTransverseProjection := by
  rw [diskPhysicalTransverseProjection_eq_half]
  with_reducible
    exact EulerNonuniqueness.General.negativeInvolutionProjection_idempotent
      (Space := PeriodicC1HolderHalf) (diskPhysicalGroup (2 * Real.pi)) diskPhysicalGroup_half_square

theorem diskPhysicalTransverseProjection_half :
    diskPhysicalTransverseProjection.comp (diskPhysicalGroup (2 * Real.pi)) = -diskPhysicalTransverseProjection ∧
    (diskPhysicalGroup (2 * Real.pi)).comp diskPhysicalTransverseProjection = -diskPhysicalTransverseProjection := by
  rw [diskPhysicalTransverseProjection_eq_half]
  with_reducible
    exact EulerNonuniqueness.General.negativeInvolutionProjection_comp
      (Space := PeriodicC1HolderHalf) (diskPhysicalGroup (2 * Real.pi)) diskPhysicalGroup_half_square

end

end EulerNonuniqueness.Paper
