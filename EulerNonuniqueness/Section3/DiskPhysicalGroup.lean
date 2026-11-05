import EulerNonuniqueness.Section3.DiskRealGroup
import EulerNonuniqueness.Section3.DiskQuadraticHomological

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalGroupHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance physicalGroupC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance physicalGroupC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance physicalGroupStateBoundedSMul : IsBoundedSMul ℝ DiskLinearState :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := DiskLinearState)
local instance physicalGroupC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance physicalGroupC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance physicalGroupReconstructionGroup : NormedAddCommGroup (DiskLinearState →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DiskLinearState) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance physicalGroupCoordinatesGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
local instance physicalGroupOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance physicalGroupOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

def diskPhysicalCoordinatesCLM : PeriodicC1HolderHalf →L[ℝ] DiskLinearState :=
  diskRadialCLM.prod diskAngularCLM

def diskPhysicalReconstructionCLM : DiskLinearState →L[ℝ] PeriodicC1HolderHalf :=
  (c1ProductCLM standardCircleBanach).coprod
    ((c1ProductCLM standardCircleBanach).comp (c1ProductCLM (c1Constant Complex.I)))

theorem diskPhysicalReconstructionCLM_apply (state : DiskLinearState) :
    diskPhysicalReconstructionCLM state = diskMaterialPerturbation state.1 state.2 := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change standardCircle label * state.1.val.1 label +
    standardCircle label * (Complex.I * state.2.val.1 label) =
    standardCircle label * (state.1.val.1 label + Complex.I * state.2.val.1 label)
  ring

def diskPhysicalGroup (time : ℝ) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  diskPhysicalReconstructionCLM.comp ((diskLinearGroupOperator time).comp diskPhysicalCoordinatesCLM)

theorem diskPhysicalGroup_apply (time : ℝ) (direction : PeriodicC1HolderHalf) :
    diskPhysicalGroup time direction =
      diskMaterialPerturbation
        (diskLinearFlow time (diskRadialCLM direction) (diskAngularCLM direction)).1
        (diskLinearFlow time (diskRadialCLM direction) (diskAngularCLM direction)).2 := by
  change diskPhysicalReconstructionCLM (diskLinearGroupOperator time (diskPhysicalCoordinatesCLM direction)) = _
  rw [diskPhysicalReconstructionCLM_apply, diskLinearGroupOperator_apply]
  rfl

theorem diskPhysicalGroup_zero : diskPhysicalGroup 0 = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  apply ContinuousLinearMap.ext
  intro direction
  rw [diskPhysicalGroup_apply, diskLinearFlow_zero]
  exact diskPhysicalCoordinates_reconstruct direction

theorem diskPhysicalGroup_add (first second : ℝ) :
    diskPhysicalGroup (first + second) = (diskPhysicalGroup first).comp (diskPhysicalGroup second) := by
  apply ContinuousLinearMap.ext
  intro direction
  have realValues := diskLinearFlow_real second (diskRadialCLM direction) (diskAngularCLM direction)
    (diskRadialPart_real direction) (diskAngularCLM_real direction)
  change diskPhysicalGroup (first + second) direction = diskPhysicalGroup first (diskPhysicalGroup second direction)
  rw [diskPhysicalGroup_apply first, diskPhysicalGroup_apply second, diskRadialCLM_apply,
    diskRadialPart_materialPerturbation _ _ realValues.1 realValues.2,
    diskAngularCLM_materialPerturbation _ _ realValues.1 realValues.2]
  rw [diskLinearFlow_add, diskPhysicalGroup_apply]

theorem diskPhysicalGroup_period : Function.Periodic diskPhysicalGroup (4 * Real.pi) := by
  intro time
  unfold diskPhysicalGroup
  rw [diskLinearGroupOperator_add, diskLinearGroupOperator_period, ContinuousLinearMap.comp_id]

def diskPhysicalGroupBound : ℝ :=
  ‖diskPhysicalReconstructionCLM‖ * diskLinearGroupBound * ‖diskPhysicalCoordinatesCLM‖

theorem diskPhysicalGroupBound_nonnegative : 0 ≤ diskPhysicalGroupBound := by
  exact mul_nonneg (mul_nonneg (norm_nonneg _) diskLinearGroupBound_nonnegative) (norm_nonneg _)

theorem diskPhysicalGroup_norm_bound (time : ℝ) (direction : PeriodicC1HolderHalf) :
    ‖diskPhysicalGroup time direction‖ ≤ diskPhysicalGroupBound * ‖direction‖ := by
  change ‖diskPhysicalReconstructionCLM (diskLinearGroupOperator time (diskPhysicalCoordinatesCLM direction))‖ ≤ _
  calc
    _ ≤ ‖diskPhysicalReconstructionCLM‖ * ‖diskLinearGroupOperator time (diskPhysicalCoordinatesCLM direction)‖ :=
      by
        with_reducible
          exact ContinuousLinearMap.le_opNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
            (E := DiskLinearState) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
            diskPhysicalReconstructionCLM _
    _ ≤ ‖diskPhysicalReconstructionCLM‖ * (diskLinearGroupBound * ‖diskPhysicalCoordinatesCLM direction‖) :=
      mul_le_mul_of_nonneg_left (diskLinearGroupOperator_norm_bound time _) (norm_nonneg _)
    _ ≤ ‖diskPhysicalReconstructionCLM‖ * (diskLinearGroupBound *
        (‖diskPhysicalCoordinatesCLM‖ * ‖direction‖)) := by
      have coefficientNonnegative := diskLinearGroupBound_nonnegative
      gcongr
      with_reducible
        exact ContinuousLinearMap.le_opNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
          (E := PeriodicC1HolderHalf) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
          diskPhysicalCoordinatesCLM direction
    _ = _ := by unfold diskPhysicalGroupBound; ring

end

end EulerNonuniqueness.Paper
