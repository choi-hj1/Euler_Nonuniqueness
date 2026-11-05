import EulerNonuniqueness.Section3.DiskTransverseQuadratic
import EulerNonuniqueness.General.ProjectedResonanceCommutation
import EulerNonuniqueness.General.InvolutionProjectionCommutation

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance neutralHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance neutralC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance neutralC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance neutralC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance neutralC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance neutralC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance neutralC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance neutralOperatorTopology : TopologicalSpace (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := DiskLinearState) (F := DiskLinearState)
local instance neutralOperatorGroup : NormedAddCommGroup (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
local instance neutralOperatorSpace : NormedSpace ℝ (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)

theorem diskTransverseProjection_group_commutes (time : ℝ) :
    diskTransverseProjection.comp (diskLinearGroupOperator time) =
      (diskLinearGroupOperator time).comp diskTransverseProjection := by
  have commutes : (diskLinearGroupOperator (2 * Real.pi)).comp (diskLinearGroupOperator time) =
      (diskLinearGroupOperator time).comp (diskLinearGroupOperator (2 * Real.pi)) := by
    rw [← diskLinearGroupOperator_add, ← diskLinearGroupOperator_add, add_comm]
  unfold diskTransverseProjection
  with_reducible
    exact EulerNonuniqueness.General.negativeInvolutionProjection_commutes (Space := DiskLinearState)
      (diskLinearGroupOperator (2 * Real.pi)) (diskLinearGroupOperator time) commutes

theorem diskResonance_transverse_inputs_zero
    (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) (first second : DiskLinearState) :
    diskTransverseProjection (diskQuadraticResonance bilinear
      (diskTransverseProjection first) (diskTransverseProjection second)) = 0 := by
  unfold diskQuadraticResonance
  rw [show 4 * Real.pi = 2 * (2 * Real.pi) by ring]
  with_reducible
    exact EulerNonuniqueness.General.transverse_resonance_on_transverse_inputs_zero (Space := DiskLinearState)
      diskLinearGroupOperator diskLinearGenerator diskTransverseProjection diskLinearGroupOperator_zero
      diskLinearGroupOperator_add diskLinearGroupOperator_generator diskTransverseProjection_group_commutes
      diskTransverseProjection_idempotent diskTransverseProjection_half.1 diskTransverseProjection_half.2
      bilinear first second

theorem diskResonance_neutral_defect_bound
    (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) (state : DiskLinearState) :
    ‖diskTransverseProjection (diskQuadraticResonance bilinear state state)‖ ≤
      ‖diskTransverseProjection‖ * ‖diskQuadraticResonance bilinear‖ * (1 + ‖diskTransverseProjection‖) *
        ‖state‖ * ‖state - diskTransverseProjection state‖ := by
  with_reducible
    exact EulerNonuniqueness.General.projected_bilinear_neutral_defect_bound (Space := DiskLinearState)
      diskTransverseProjection (diskQuadraticResonance bilinear) (diskResonance_transverse_inputs_zero bilinear) state

theorem diskResonance_cubic_of_neutral_defect
    (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) (state : DiskLinearState)
    {neutralBound : ℝ} (neutralNonnegative : 0 ≤ neutralBound)
    (neutralDefect : ‖state - diskTransverseProjection state‖ ≤ neutralBound * ‖state‖ ^ 2) :
    ‖diskTransverseProjection (diskQuadraticResonance bilinear state state)‖ ≤
      (‖diskTransverseProjection‖ * ‖diskQuadraticResonance bilinear‖ * (1 + ‖diskTransverseProjection‖) * neutralBound) *
        ‖state‖ ^ 3 := by
  calc
    _ ≤ ‖diskTransverseProjection‖ * ‖diskQuadraticResonance bilinear‖ * (1 + ‖diskTransverseProjection‖) *
        ‖state‖ * ‖state - diskTransverseProjection state‖ := diskResonance_neutral_defect_bound bilinear state
    _ ≤ ‖diskTransverseProjection‖ * ‖diskQuadraticResonance bilinear‖ * (1 + ‖diskTransverseProjection‖) *
        ‖state‖ * (neutralBound * ‖state‖ ^ 2) := by gcongr
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
