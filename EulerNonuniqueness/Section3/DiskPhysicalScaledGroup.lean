import EulerNonuniqueness.Section3.DiskPhysicalGenerator
import EulerNonuniqueness.General.ScaledLinearGroup

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] physicalGeneratorC1Space physicalGeneratorC1ContinuousAdd
  physicalGeneratorC1UniformAdd physicalGeneratorC1BoundedSMul
  physicalGeneratorOperatorGroup physicalGeneratorOperatorSpace

local instance physicalScaledOperatorModule : Module ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ)
    (M := PeriodicC1HolderHalf) (M₃ := PeriodicC1HolderHalf) (σ₁₃ := RingHom.id ℝ)

local instance physicalScaledOperatorBoundedSMul :
    IsBoundedSMul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ)
    (E := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)

def diskPhysicalScaledGroup (frequency time : ℝ) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  diskPhysicalGroup (frequency * time)

theorem diskPhysicalScaledGroup_generator (frequency time : ℝ) :
    HasDerivAt (diskPhysicalScaledGroup frequency)
      ((diskPhysicalScaledGroup frequency time).comp (frequency • diskRotatingDerivative)) time := by
  unfold diskPhysicalScaledGroup
  with_reducible
    exact EulerNonuniqueness.General.linearGroup_scaled_hasDerivAt
      (Space := PeriodicC1HolderHalf)
      diskPhysicalGroup diskRotatingDerivative diskPhysicalGroup_generator frequency time

theorem diskPhysicalScaledGroup_norm_bound (frequency time : ℝ) (direction : PeriodicC1HolderHalf) :
    ‖diskPhysicalScaledGroup frequency time direction‖ ≤ diskPhysicalGroupBound * ‖direction‖ :=
  diskPhysicalGroup_norm_bound (frequency * time) direction

end

end EulerNonuniqueness.Paper
