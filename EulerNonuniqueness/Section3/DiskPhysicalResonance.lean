import EulerNonuniqueness.Section3.DiskPhysicalSpectral
import EulerNonuniqueness.Section3.ContourVelocityBoundedBilinear
import EulerNonuniqueness.General.ProjectedResonanceCommutation
import EulerNonuniqueness.General.InvolutionProjectionCommutation

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalResonanceHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance physicalResonanceC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem diskPhysicalTransverseProjection_group_commutes (time : ℝ) :
    diskPhysicalTransverseProjection.comp (diskPhysicalGroup time) =
      (diskPhysicalGroup time).comp diskPhysicalTransverseProjection := by
  have commutes : (diskPhysicalGroup (2 * Real.pi)).comp (diskPhysicalGroup time) =
      (diskPhysicalGroup time).comp (diskPhysicalGroup (2 * Real.pi)) := by
    rw [← diskPhysicalGroup_add, ← diskPhysicalGroup_add, add_comm]
  rw [diskPhysicalTransverseProjection_eq_half]
  with_reducible
    exact EulerNonuniqueness.General.negativeInvolutionProjection_commutes
      (Space := PeriodicC1HolderHalf) (diskPhysicalGroup (2 * Real.pi)) (diskPhysicalGroup time) commutes

theorem diskPhysicalResonance_transverse_inputs_zero
    (bilinear : EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf)
    (first second : PeriodicC1HolderHalf) :
    diskPhysicalTransverseProjection
      (EulerNonuniqueness.General.quadraticResonance (Space := PeriodicC1HolderHalf)
        diskPhysicalGroup (4 * Real.pi) bilinear
        (diskPhysicalTransverseProjection first) (diskPhysicalTransverseProjection second)) = 0 := by
  rw [show 4 * Real.pi = 2 * (2 * Real.pi) by ring]
  with_reducible
    exact EulerNonuniqueness.General.transverse_resonance_on_transverse_inputs_zero
      (Space := PeriodicC1HolderHalf) diskPhysicalGroup diskRotatingDerivative diskPhysicalTransverseProjection
      diskPhysicalGroup_zero diskPhysicalGroup_add diskPhysicalGroup_generator
      diskPhysicalTransverseProjection_group_commutes diskPhysicalTransverseProjection_idempotent
      diskPhysicalTransverseProjection_half.1 diskPhysicalTransverseProjection_half.2 bilinear first second

theorem diskActualQuadraticResonance_transverse_inputs_zero
    {radius : ℝ} (positive : 0 < radius) (small : radius < min 1 (2 / (3 * Real.pi)))
    (first second : PeriodicC1HolderHalf) :
    diskPhysicalTransverseProjection
      (EulerNonuniqueness.General.quadraticResonance (Space := PeriodicC1HolderHalf)
        diskPhysicalGroup (4 * Real.pi)
        (contourVelocityBilinearCLM standardCircleBanach (innerRadius := 0) (outerRadius := radius)
          (by norm_num) positive small (by simp))
        (diskPhysicalTransverseProjection first) (diskPhysicalTransverseProjection second)) = 0 :=
  diskPhysicalResonance_transverse_inputs_zero _ first second

end

end EulerNonuniqueness.Paper
