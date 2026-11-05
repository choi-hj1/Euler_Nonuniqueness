import EulerNonuniqueness.Section3.DiskPhysicalScaledGroup
import EulerNonuniqueness.General.LinearGroupNormRecovery

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance scaledGroupRecoveryC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] physicalGeneratorC1Space physicalGeneratorC1ContinuousAdd
  physicalGeneratorC1UniformAdd physicalGeneratorC1BoundedSMul
  physicalGeneratorOperatorGroup physicalGeneratorOperatorSpace

theorem diskPhysicalScaledGroup_apply_neg (frequency time : ℝ) (data : PeriodicC1HolderHalf) :
    diskPhysicalScaledGroup frequency time (diskPhysicalScaledGroup frequency (-time) data) = data := by
  unfold diskPhysicalScaledGroup
  with_reducible_and_instances
    exact EulerNonuniqueness.General.linear_group_scaled_apply_neg
      diskPhysicalGroup diskPhysicalGroup_zero diskPhysicalGroup_add frequency time data

theorem diskPhysicalScaledGroup_norm_recovery (frequency time : ℝ) (data : PeriodicC1HolderHalf) :
    ‖data‖ ≤ diskPhysicalGroupBound * ‖diskPhysicalScaledGroup frequency (-time) data‖ := by
  unfold diskPhysicalScaledGroup
  with_reducible_and_instances
    exact EulerNonuniqueness.General.linear_group_scaled_norm_recovery
      diskPhysicalGroup diskPhysicalGroup_zero diskPhysicalGroup_add
      diskPhysicalGroupBound diskPhysicalGroup_norm_bound frequency time data

end EulerNonuniqueness.Paper
