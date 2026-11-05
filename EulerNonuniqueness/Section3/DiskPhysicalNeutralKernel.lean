import EulerNonuniqueness.Section3.DiskPhysicalSpectral
import EulerNonuniqueness.General.LinearGroupFixedVector

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalNeutralHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance physicalNeutralC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem diskRotatingDerivative_neutral_defect_zero (direction : PeriodicC1HolderHalf) :
    diskRotatingDerivative (direction - diskPhysicalTransverseProjection direction) = 0 := by
  rw [diskPhysical_neutral_decomposition, diskRotatingDerivative_apply]
  have actual := disk_material_generator_intertwines
    (periodicMeanProjectionCCLM (diskRadialPart direction)) (diskNeutralCLM direction)
    (periodicMeanProjection_real _ (diskRadialPart_real direction)) (diskNeutralCLM_real direction)
  rw [actual, diskLinearGenerator_apply, periodicHilbertC1_meanProjection]
  have meanZero : periodicMeanZeroPartCCLM (periodicMeanProjectionCCLM (diskRadialPart direction)) = 0 := by
    change periodicMeanProjectionCCLM (diskRadialPart direction) -
      periodicMeanProjectionCCLM (periodicMeanProjectionCCLM (diskRadialPart direction)) = 0
    rw [periodicMeanProjectionCCLM_idempotent]
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (periodicMeanProjectionCCLM (diskRadialPart direction)).val.1 label -
      (periodicMeanProjectionCCLM (diskRadialPart direction)).val.1 label = 0
    exact sub_self _
  rw [meanZero]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label * ((-1 / 2 : ℝ) • (0 : ℂ) + Complex.I * ((-1 / 2 : ℝ) • (0 : ℂ))) = 0
  simp only [smul_zero, mul_zero, zero_add]

theorem diskPhysicalGroup_neutral_defect_fixed (direction : PeriodicC1HolderHalf) (time : ℝ) :
    diskPhysicalGroup time (direction - diskPhysicalTransverseProjection direction) =
      direction - diskPhysicalTransverseProjection direction := by
  with_reducible
    exact EulerNonuniqueness.General.linearGroup_fixed_of_generator_zero
      (Space := PeriodicC1HolderHalf) diskPhysicalGroup diskRotatingDerivative diskPhysicalGroup_zero
      diskPhysicalGroup_generator (diskRotatingDerivative_neutral_defect_zero direction) time

theorem diskPhysicalExponential_relabel_tangent_fixed (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) (time : ℝ) :
    EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf) diskRotatingDerivative time
      (diskRelabelGenerator angular standardCircleBanach) = diskRelabelGenerator angular standardCircleBanach := by
  with_reducible
    exact EulerNonuniqueness.General.linearExponentialGroup_fixed_of_generator_zero
      (Space := PeriodicC1HolderHalf) diskRotatingDerivative
      (diskRotatingDerivative_relabel_tangent_zero angular realValues) time

end

end EulerNonuniqueness.Paper
