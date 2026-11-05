import EulerNonuniqueness.Section3.DiskQuadraticHomological
import EulerNonuniqueness.General.ProjectedAntipodalQuadratic
import EulerNonuniqueness.General.InvolutionProjection
import EulerNonuniqueness.General.ProjectedQuadraticResonance

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance transverseHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance transverseC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance transverseC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance transverseC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance transverseC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance transverseC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance transverseC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance transverseOperatorTopology : TopologicalSpace (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := DiskLinearState) (F := DiskLinearState)
local instance transverseOperatorGroup : NormedAddCommGroup (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
local instance transverseOperatorSpace : NormedSpace ℝ (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)

def diskTransverseProjection : DiskLinearState →L[ℝ] DiskLinearState :=
  EulerNonuniqueness.General.negativeInvolutionProjection (Space := DiskLinearState) (diskLinearGroupOperator (2 * Real.pi))

theorem diskTransverseProjection_eq_cos : diskTransverseProjection = diskLinearCosOperator := by
  have atZero := diskLinearGroupOperator_zero
  unfold diskLinearGroupOperator at atZero
  simp only [zero_div, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero] at atZero
  unfold diskTransverseProjection EulerNonuniqueness.General.negativeInvolutionProjection diskLinearGroupOperator
  rw [show 2 * Real.pi / 2 = Real.pi by ring, Real.cos_pi, Real.sin_pi]
  simp only [neg_smul, one_smul, zero_smul, add_zero]
  rw [← atZero]
  module

theorem diskTransverseProjection_apply (state : DiskLinearState) :
    diskTransverseProjection state =
      (periodicMeanZeroPartCCLM state.1, -periodicHilbertC1 state.1) := by
  rw [diskTransverseProjection_eq_cos]
  rfl

theorem diskLinearGroupOperator_half_square :
    (diskLinearGroupOperator (2 * Real.pi)).comp (diskLinearGroupOperator (2 * Real.pi)) =
      ContinuousLinearMap.id ℝ DiskLinearState := by
  rw [← diskLinearGroupOperator_add, show 2 * Real.pi + 2 * Real.pi = 4 * Real.pi by ring,
    diskLinearGroupOperator_period]

theorem diskTransverseProjection_half :
    diskTransverseProjection.comp (diskLinearGroupOperator (2 * Real.pi)) = -diskTransverseProjection ∧
      (diskLinearGroupOperator (2 * Real.pi)).comp diskTransverseProjection = -diskTransverseProjection := by
  unfold diskTransverseProjection
  with_reducible
    exact EulerNonuniqueness.General.negativeInvolutionProjection_comp (Space := DiskLinearState)
      (diskLinearGroupOperator (2 * Real.pi)) diskLinearGroupOperator_half_square

theorem diskTransverseProjection_idempotent :
    diskTransverseProjection.comp diskTransverseProjection = diskTransverseProjection := by
  unfold diskTransverseProjection
  with_reducible
    exact EulerNonuniqueness.General.negativeInvolutionProjection_idempotent (Space := DiskLinearState)
      (diskLinearGroupOperator (2 * Real.pi)) diskLinearGroupOperator_half_square

def diskTransverseQuadratic (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) :
    EulerNonuniqueness.General.BilinearEnd DiskLinearState :=
  EulerNonuniqueness.General.projectedQuadratic diskTransverseProjection bilinear

theorem diskTransverseQuadratic_input (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState)
    (first second : DiskLinearState) :
    diskTransverseQuadratic bilinear (diskTransverseProjection first) (diskTransverseProjection second) =
      diskTransverseQuadratic bilinear first second := by
  unfold diskTransverseQuadratic
  with_reducible
    exact EulerNonuniqueness.General.projectedQuadratic_input (Space := DiskLinearState)
      diskTransverseProjection diskTransverseProjection_idempotent bilinear first second

theorem diskTransverseQuadratic_output (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState)
    (first second : DiskLinearState) :
    diskTransverseProjection (diskTransverseQuadratic bilinear first second) =
      diskTransverseQuadratic bilinear first second := by
  unfold diskTransverseQuadratic
  with_reducible
    exact EulerNonuniqueness.General.projectedQuadratic_output (Space := DiskLinearState)
      diskTransverseProjection diskTransverseProjection_idempotent bilinear first second

theorem diskTransverseQuadratic_resonance_zero
    (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) :
    diskQuadraticResonance (diskTransverseQuadratic bilinear) = 0 := by
  unfold diskQuadraticResonance diskTransverseQuadratic
  rw [show 4 * Real.pi = 2 * (2 * Real.pi) by ring]
  with_reducible
    exact EulerNonuniqueness.General.projectedQuadratic_resonance_zero (Space := DiskLinearState)
      diskLinearGroupOperator diskLinearGenerator diskTransverseProjection
      diskLinearGroupOperator_zero diskLinearGroupOperator_add diskLinearGroupOperator_generator
      diskTransverseProjection_idempotent diskTransverseProjection_half.1 diskTransverseProjection_half.2 bilinear

theorem diskTransverseQuadratic_homological_identity
    (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) :
    EulerNonuniqueness.General.quadraticCommutator diskLinearGenerator
      (diskQuadraticHomologicalSolution (diskTransverseQuadratic bilinear)) = diskTransverseQuadratic bilinear := by
  rw [disk_quadratic_homological_identity, diskTransverseQuadratic_resonance_zero, sub_zero]

end

end EulerNonuniqueness.Paper
