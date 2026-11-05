import EulerNonuniqueness.Section3.DiskLinearGroup
import EulerNonuniqueness.General.LinearGroupGenerator

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance diskOperatorHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance diskOperatorC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance diskOperatorC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance diskOperatorC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance diskOperatorC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance diskOperatorC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance diskOperatorC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)

abbrev DiskLinearState := PeriodicC1HolderHalf × PeriodicC1HolderHalf

local instance diskOperatorStateBoundedSMul : IsBoundedSMul ℝ DiskLinearState :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := DiskLinearState)
local instance diskOperatorComponentGroup : NormedAddCommGroup (DiskLinearState →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DiskLinearState) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance diskOperatorTopology : TopologicalSpace (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := DiskLinearState) (F := DiskLinearState)
local instance diskOperatorNormedGroup : NormedAddCommGroup (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
local instance diskOperatorSpace : NormedSpace ℝ (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)

def diskLinearMeanOperator : DiskLinearState →L[ℝ] DiskLinearState :=
  ((periodicMeanProjectionCCLM.restrictScalars ℝ).comp
    (ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf)).prod
      ((ContinuousLinearMap.snd ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf) +
        periodicHilbertC1CLM.comp (ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf))

def diskLinearCosOperator : DiskLinearState →L[ℝ] DiskLinearState :=
  ((periodicMeanZeroPartCCLM.restrictScalars ℝ).comp
    (ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf)).prod
      (-(periodicHilbertC1CLM.comp (ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf)))

def diskLinearSinOperator : DiskLinearState →L[ℝ] DiskLinearState :=
  (-(periodicHilbertC1CLM.comp (ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf))).prod
    (-((periodicMeanZeroPartCCLM.restrictScalars ℝ).comp
      (ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf)))

def diskLinearGroupOperator (time : ℝ) : DiskLinearState →L[ℝ] DiskLinearState :=
  diskLinearMeanOperator + Real.cos (time / 2) • diskLinearCosOperator +
    Real.sin (time / 2) • diskLinearSinOperator

theorem diskLinearGroupOperator_apply (time : ℝ) (data : DiskLinearState) :
    diskLinearGroupOperator time data = diskLinearFlow time data.1 data.2 := by
  apply Prod.ext
  · apply PeriodicC1HolderHalf.ext_value
    intro label
    change (periodicMeanProjectionCCLM data.1).val.1 label +
        Real.cos (time / 2) • (periodicMeanZeroPartCCLM data.1).val.1 label +
        Real.sin (time / 2) • (-(periodicHilbertC1 data.1).val.1 label) =
      (periodicMeanProjectionCCLM data.1).val.1 label +
        Real.cos (time / 2) • (periodicMeanZeroPartCCLM data.1).val.1 label +
        (-Real.sin (time / 2)) • (periodicHilbertC1 data.1).val.1 label
    simp only [Complex.real_smul]
    push_cast
    ring
  · change (data.2 + periodicHilbertC1 data.1) +
      Real.cos (time / 2) • (-periodicHilbertC1 data.1) +
      Real.sin (time / 2) • (-periodicMeanZeroPartCCLM data.1) =
      data.2 + periodicHilbertC1 data.1 - periodicHilbertC1 (periodicHilbertFlow time data.1)
    rw [periodicHilbertC1_flow]
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (data.2.val.1 label + (periodicHilbertC1 data.1).val.1 label) +
        Real.cos (time / 2) • (-(periodicHilbertC1 data.1).val.1 label) +
        Real.sin (time / 2) • (-(periodicMeanZeroPartCCLM data.1).val.1 label) =
      data.2.val.1 label + (periodicHilbertC1 data.1).val.1 label -
        (Real.cos (time / 2) • (periodicHilbertC1 data.1).val.1 label +
          Real.sin (time / 2) • (periodicMeanZeroPartCCLM data.1).val.1 label)
    simp only [Complex.real_smul]
    ring

theorem diskLinearGroupOperator_zero : diskLinearGroupOperator 0 = ContinuousLinearMap.id ℝ DiskLinearState := by
  apply ContinuousLinearMap.ext
  intro data
  rw [diskLinearGroupOperator_apply, diskLinearFlow_zero]
  rfl

theorem diskLinearGroupOperator_add (first second : ℝ) :
    diskLinearGroupOperator (first + second) =
      (diskLinearGroupOperator first).comp (diskLinearGroupOperator second) := by
  apply ContinuousLinearMap.ext
  intro data
  rw [ContinuousLinearMap.comp_apply, diskLinearGroupOperator_apply,
    diskLinearGroupOperator_apply, diskLinearGroupOperator_apply, diskLinearFlow_add]

def diskLinearGroupDerivative (time : ℝ) : DiskLinearState →L[ℝ] DiskLinearState :=
  (-Real.sin (time / 2) * (1 / 2)) • diskLinearCosOperator +
    (Real.cos (time / 2) * (1 / 2)) • diskLinearSinOperator

theorem diskLinearGroupOperator_hasDerivAt (time : ℝ) :
    HasDerivAt diskLinearGroupOperator (diskLinearGroupDerivative time) time := by
  have halfDerivative : HasDerivAt (fun current : ℝ => current / 2) (1 / 2) time := by
    simpa only [id_eq] using (hasDerivAt_id time).div_const 2
  exact ((halfDerivative.cos.smul_const diskLinearCosOperator).const_add diskLinearMeanOperator).add
    (halfDerivative.sin.smul_const diskLinearSinOperator)

def diskLinearGenerator : DiskLinearState →L[ℝ] DiskLinearState := diskLinearGroupDerivative 0

theorem diskLinearGroupOperator_generator (time : ℝ) :
    HasDerivAt diskLinearGroupOperator ((diskLinearGroupOperator time).comp diskLinearGenerator) time := by
  change HasDerivAt diskLinearGroupOperator ((diskLinearGroupOperator time).comp (diskLinearGroupDerivative 0)) time
  exact EulerNonuniqueness.General.linearGroup_hasDerivAt_right_generator (Space := DiskLinearState)
    diskLinearGroupOperator diskLinearGroupDerivative diskLinearGroupOperator_add diskLinearGroupOperator_hasDerivAt time

theorem diskLinearGenerator_apply (data : DiskLinearState) :
    diskLinearGenerator data =
      ((-1 / 2 : ℝ) • periodicHilbertC1 data.1, (-1 / 2 : ℝ) • periodicMeanZeroPartCCLM data.1) := by
  apply Prod.ext <;> apply PeriodicC1HolderHalf.ext_value <;> intro label
  · change (-Real.sin (0 / 2) * (1 / 2)) • (periodicMeanZeroPartCCLM data.1).val.1 label +
      (Real.cos (0 / 2) * (1 / 2)) • (-(periodicHilbertC1 data.1).val.1 label) =
      (-1 / 2 : ℝ) • (periodicHilbertC1 data.1).val.1 label
    simp [Complex.real_smul]
    ring
  · change (-Real.sin (0 / 2) * (1 / 2)) • (-(periodicHilbertC1 data.1).val.1 label) +
      (Real.cos (0 / 2) * (1 / 2)) • (-(periodicMeanZeroPartCCLM data.1).val.1 label) =
      (-1 / 2 : ℝ) • (periodicMeanZeroPartCCLM data.1).val.1 label
    simp [Complex.real_smul]
    ring

def diskLinearGroupBound : ℝ := 2 * (3 + 10 * periodicHilbertBound + 4 * periodicHilbertBound ^ 2)

theorem diskLinearGroupBound_nonnegative : 0 ≤ diskLinearGroupBound := by
  unfold diskLinearGroupBound
  have boundNonnegative := periodicHilbertBound_nonneg
  positivity

theorem diskLinearGroupOperator_norm_bound (time : ℝ) (data : DiskLinearState) :
    ‖diskLinearGroupOperator time data‖ ≤ diskLinearGroupBound * ‖data‖ := by
  rw [diskLinearGroupOperator_apply]
  have firstBound : ‖data.1‖ ≤ ‖data‖ := le_max_left _ _
  have secondBound : ‖data.2‖ ≤ ‖data‖ := le_max_right _ _
  have coefficientNonnegative : 0 ≤ 3 + 10 * periodicHilbertBound + 4 * periodicHilbertBound ^ 2 := by
    have boundNonnegative := periodicHilbertBound_nonneg
    positivity
  calc
    _ ≤ ‖(diskLinearFlow time data.1 data.2).1‖ + ‖(diskLinearFlow time data.1 data.2).2‖ :=
      max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
    _ ≤ (3 + 10 * periodicHilbertBound + 4 * periodicHilbertBound ^ 2) * (‖data.1‖ + ‖data.2‖) :=
      diskLinearFlow_uniform_bound time data.1 data.2
    _ ≤ (3 + 10 * periodicHilbertBound + 4 * periodicHilbertBound ^ 2) * (‖data‖ + ‖data‖) :=
      mul_le_mul_of_nonneg_left (add_le_add firstBound secondBound) coefficientNonnegative
    _ = _ := by unfold diskLinearGroupBound; ring

end

end EulerNonuniqueness.Paper
