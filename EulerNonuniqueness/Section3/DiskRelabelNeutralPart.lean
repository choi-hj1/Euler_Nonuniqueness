import EulerNonuniqueness.Section3.DiskPhysicalProjection
import EulerNonuniqueness.Section3.DiskAreaMeanProjection

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance relabelNeutralHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance relabelNeutralC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def diskRelabelNeutralCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (c1ProductCLM standardCircleBanach).comp ((c1ProductCLM (c1Constant Complex.I)).comp diskNeutralCLM)

theorem diskRelabelNeutralCLM_apply (increment : PeriodicC1HolderHalf) :
    diskRelabelNeutralCLM increment = diskMaterialPerturbation 0 (diskNeutralCLM increment) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label * (Complex.I * (diskNeutralCLM increment).val.1 label) =
    standardCircle label * (0 + Complex.I * (diskNeutralCLM increment).val.1 label)
  ring

theorem diskPhysical_relabel_neutral_decomposition (increment : PeriodicC1HolderHalf) :
    increment - diskRelabelNeutralCLM increment = diskPhysicalTransverseProjection increment +
      c1Product standardCircleBanach (c1Constant (diskRadialMean increment : ℂ)) := by
  have neutral := diskPhysical_neutral_decomposition increment
  rw [periodicMeanProjection_diskRadialPart] at neutral
  rw [diskRelabelNeutralCLM_apply]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  have pointwise := congrArg (fun data : PeriodicC1HolderHalf => data.val.1 label) neutral
  change increment.val.1 label - (diskPhysicalTransverseProjection increment).val.1 label =
    standardCircle label * ((diskRadialMean increment : ℂ) +
      Complex.I * (diskNeutralCLM increment).val.1 label) at pointwise
  change increment.val.1 label - standardCircle label * (0 + Complex.I * (diskNeutralCLM increment).val.1 label) =
    (diskPhysicalTransverseProjection increment).val.1 label + standardCircle label * (diskRadialMean increment : ℂ)
  linear_combination pointwise

end

end EulerNonuniqueness.Paper
