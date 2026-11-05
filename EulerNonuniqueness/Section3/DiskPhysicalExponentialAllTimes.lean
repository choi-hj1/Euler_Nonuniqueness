import EulerNonuniqueness.Section3.DiskPhysicalExponential
import EulerNonuniqueness.General.LinearGroupExponentialAllTimes

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalAllExpHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance physicalAllExpC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance physicalAllExpC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance physicalAllExpC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance physicalAllExpC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance physicalAllExpOperatorTopology : TopologicalSpace (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
local instance physicalAllExpOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance physicalAllExpOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem diskPhysicalGroup_eq_exponential_all_times (time : ℝ) :
    diskPhysicalGroup time = EulerNonuniqueness.General.linearExponentialGroup
      (Space := PeriodicC1HolderHalf) diskRotatingDerivative time := by
  with_reducible
    exact EulerNonuniqueness.General.linearGroup_eq_exponential_all_times
      (Space := PeriodicC1HolderHalf) diskPhysicalGroup diskRotatingDerivative diskPhysicalGroup_zero
      diskPhysicalGroup_add diskPhysicalGroup_generator time

end

end EulerNonuniqueness.Paper
