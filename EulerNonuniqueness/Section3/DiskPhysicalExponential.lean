import EulerNonuniqueness.Section3.DiskPhysicalGenerator
import EulerNonuniqueness.General.LinearGroupExponentialIdentification
import EulerNonuniqueness.General.LinearExponentialGroup

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalExpHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance physicalExpC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance physicalExpC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance physicalExpC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance physicalExpC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance physicalExpOperatorTopology : TopologicalSpace (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
local instance physicalExpOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance physicalExpOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem diskPhysicalGroup_eq_exp {time : ℝ} (nonnegative : 0 ≤ time) :
    diskPhysicalGroup time = EulerNonuniqueness.General.linearExponentialGroup
      (Space := PeriodicC1HolderHalf) diskRotatingDerivative time := by
  unfold EulerNonuniqueness.General.linearExponentialGroup
  with_reducible
    exact EulerNonuniqueness.General.linearGroup_eq_exp_of_nonnegative
      (Space := PeriodicC1HolderHalf) diskPhysicalGroup diskRotatingDerivative diskPhysicalGroup_zero
      diskPhysicalGroup_add diskPhysicalGroup_generator nonnegative

theorem diskRotatingDerivative_exp_period :
    EulerNonuniqueness.General.linearExponentialGroup (Space := PeriodicC1HolderHalf)
      diskRotatingDerivative (4 * Real.pi) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  rw [← diskPhysicalGroup_eq_exp (by positivity : 0 ≤ 4 * Real.pi)]
  have actual := diskPhysicalGroup_period (0 : ℝ)
  simpa only [zero_add, diskPhysicalGroup_zero] using actual

end

end EulerNonuniqueness.Paper
