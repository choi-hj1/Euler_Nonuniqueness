import EulerNonuniqueness.Section3.DiskPhysicalGenerator
import EulerNonuniqueness.Section3.DiskTransverseQuadratic

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalProjectionHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance physicalProjectionC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance physicalProjectionOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance physicalProjectionOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def diskPhysicalTransverseProjection : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  diskPhysicalReconstructionCLM.comp (diskTransverseProjection.comp diskPhysicalCoordinatesCLM)

theorem diskPhysicalTransverseProjection_apply (direction : PeriodicC1HolderHalf) :
    diskPhysicalTransverseProjection direction = diskMaterialPerturbation
      (periodicMeanZeroPartCCLM (diskRadialPart direction))
      (-periodicHilbertC1 (diskRadialPart direction)) := by
  change diskPhysicalReconstructionCLM (diskTransverseProjection (diskPhysicalCoordinatesCLM direction)) = _
  rw [diskPhysicalReconstructionCLM_apply, diskTransverseProjection_apply]
  rfl

theorem diskPhysical_neutral_decomposition (direction : PeriodicC1HolderHalf) :
    direction - diskPhysicalTransverseProjection direction =
      diskMaterialPerturbation (periodicMeanProjectionCCLM (diskRadialPart direction))
        (diskNeutralCLM direction) := by
  rw [diskPhysicalTransverseProjection_apply, diskNeutralCLM_apply]
  nth_rw 1 [← diskPhysicalCoordinates_reconstruct direction]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label * ((diskRadialPart direction).val.1 label +
      Complex.I * (diskAngularCLM direction).val.1 label) -
    standardCircle label * ((diskRadialPart direction).val.1 label -
      (periodicMeanProjectionCCLM (diskRadialPart direction)).val.1 label +
      Complex.I * -(periodicHilbertC1 (diskRadialPart direction)).val.1 label) =
    standardCircle label * ((periodicMeanProjectionCCLM (diskRadialPart direction)).val.1 label +
      Complex.I * ((diskAngularCLM direction).val.1 label +
        (periodicHilbertC1 (diskRadialPart direction)).val.1 label))
  ring

end

end EulerNonuniqueness.Paper
