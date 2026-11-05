import EulerNonuniqueness.Section3.DiskStationaryManifold
import EulerNonuniqueness.Section3.DiskRelabelNeutralPart

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance angularNeutralProjectionC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

local instance angularNeutralProjectionC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem diskNeutralCLM_relabelNeutral (data : PeriodicC1HolderHalf) :
    diskNeutralCLM (diskRelabelNeutralCLM data) = diskNeutralCLM data := by
  rw [diskRelabelNeutralCLM_apply]
  have actual := diskNeutralCLM_material_constant 0 (diskNeutralCLM data) (diskNeutralCLM_real data)
  have constantZero : c1Constant (0 : ℂ) = 0 := c1ConstantCLM.map_zero
  simpa only [Complex.ofReal_zero, constantZero] using actual

theorem diskNeutralCLM_norm_le_relabelNeutral (data : PeriodicC1HolderHalf) :
    ‖diskNeutralCLM data‖ ≤ ‖diskNeutralCLM‖ * ‖diskRelabelNeutralCLM data‖ := by
  rw [← diskNeutralCLM_relabelNeutral data]
  exact diskNeutralCLM.le_opNorm _

theorem diskNeutralCLM_hasDerivAt_of_relabelNeutral
    {curve : ℝ → PeriodicC1HolderHalf} {time : ℝ} {velocity : PeriodicC1HolderHalf}
    (derivative : HasDerivAt (fun current => diskRelabelNeutralCLM (curve current)) velocity time) :
    HasDerivAt (fun current => diskNeutralCLM (curve current)) (diskNeutralCLM velocity) time := by
  have actual := diskNeutralCLM.hasFDerivAt.comp_hasDerivAt time derivative
  simpa only [Function.comp_def, diskNeutralCLM_relabelNeutral] using actual

end EulerNonuniqueness.Paper
