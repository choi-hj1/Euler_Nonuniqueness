import EulerNonuniqueness.Section3.DiskPhysicalGroup
import EulerNonuniqueness.General.LinearOperatorSandwich

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalGeneratorHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance physicalGeneratorC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance physicalGeneratorC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance physicalGeneratorC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance physicalGeneratorC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance physicalGeneratorReconstructionGroup : NormedAddCommGroup (DiskLinearState →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DiskLinearState) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance physicalGeneratorReconstructionSpace : NormedSpace ℝ (DiskLinearState →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := DiskLinearState) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance physicalGeneratorCoordinatesGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
local instance physicalGeneratorCoordinatesSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
local instance physicalGeneratorStateOperatorGroup : NormedAddCommGroup (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
local instance physicalGeneratorStateOperatorSpace : NormedSpace ℝ (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
local instance physicalGeneratorOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance physicalGeneratorOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def diskPhysicalGroupDerivative (time : ℝ) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  diskPhysicalReconstructionCLM.comp ((diskLinearGroupDerivative time).comp diskPhysicalCoordinatesCLM)

theorem diskPhysicalGroup_hasDerivAt (time : ℝ) :
    HasDerivAt diskPhysicalGroup (diskPhysicalGroupDerivative time) time := by
  unfold diskPhysicalGroup diskPhysicalGroupDerivative
  with_reducible
    exact EulerNonuniqueness.General.linearOperatorSandwich_hasDerivAt
      (Domain := PeriodicC1HolderHalf) (Middle := DiskLinearState)
      diskPhysicalReconstructionCLM diskPhysicalCoordinatesCLM (diskLinearGroupOperator_hasDerivAt time)

theorem diskPhysicalGroupDerivative_zero : diskPhysicalGroupDerivative 0 = diskRotatingDerivative := by
  apply ContinuousLinearMap.ext
  intro direction
  change diskPhysicalReconstructionCLM (diskLinearGenerator (diskPhysicalCoordinatesCLM direction)) =
    diskRotatingDerivative direction
  rw [diskPhysicalReconstructionCLM_apply]
  have actual := disk_material_generator_intertwines (diskRadialCLM direction) (diskAngularCLM direction)
    (diskRadialPart_real direction) (diskAngularCLM_real direction)
  rw [diskPhysicalCoordinates_reconstruct, ← diskRotatingDerivative_apply] at actual
  exact actual.symm

theorem diskPhysicalGroup_generator (time : ℝ) :
    HasDerivAt diskPhysicalGroup ((diskPhysicalGroup time).comp diskRotatingDerivative) time := by
  have actual := EulerNonuniqueness.General.linearGroup_hasDerivAt_right_generator
    (Space := PeriodicC1HolderHalf) diskPhysicalGroup diskPhysicalGroupDerivative
    diskPhysicalGroup_add diskPhysicalGroup_hasDerivAt time
  rw [diskPhysicalGroupDerivative_zero] at actual
  exact actual

end

end EulerNonuniqueness.Paper
