import EulerNonuniqueness.Section3.DiskGroupOperators
import EulerNonuniqueness.General.PeriodicQuadraticBounds

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance diskQuadraticHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance diskQuadraticC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance diskQuadraticC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance diskQuadraticC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance diskQuadraticC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance diskQuadraticC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance diskQuadraticC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance diskQuadraticOperatorTopology : TopologicalSpace (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := DiskLinearState) (F := DiskLinearState)
local instance diskQuadraticOperatorGroup : NormedAddCommGroup (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
local instance diskQuadraticOperatorSpace : NormedSpace ℝ (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)

theorem diskLinearGroupOperator_period :
    diskLinearGroupOperator (4 * Real.pi) = ContinuousLinearMap.id ℝ DiskLinearState := by
  rw [← diskLinearGroupOperator_zero]
  unfold diskLinearGroupOperator
  rw [show 4 * Real.pi / 2 = 2 * Real.pi by ring, Real.cos_two_pi, Real.sin_two_pi]
  simp

def diskQuadraticResonance (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) : EulerNonuniqueness.General.BilinearEnd DiskLinearState :=
  EulerNonuniqueness.General.quadraticResonance diskLinearGroupOperator (4 * Real.pi) bilinear

def diskQuadraticHomologicalSolution (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) : EulerNonuniqueness.General.BilinearEnd DiskLinearState :=
  EulerNonuniqueness.General.quadraticHomologicalSolution diskLinearGroupOperator (4 * Real.pi) bilinear

theorem disk_quadratic_homological_identity (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) :
    EulerNonuniqueness.General.quadraticCommutator diskLinearGenerator (diskQuadraticHomologicalSolution bilinear) =
      bilinear - diskQuadraticResonance bilinear := by
  unfold diskQuadraticHomologicalSolution diskQuadraticResonance
  with_reducible
    exact EulerNonuniqueness.General.quadratic_homological_identity (Space := DiskLinearState)
      diskLinearGroupOperator diskLinearGenerator (by positivity : 0 < 4 * Real.pi)
      diskLinearGroupOperator_zero diskLinearGroupOperator_add diskLinearGroupOperator_generator
      diskLinearGroupOperator_period bilinear

theorem disk_quadratic_resonance_commutator_zero (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) :
    EulerNonuniqueness.General.quadraticCommutator diskLinearGenerator (diskQuadraticResonance bilinear) = 0 := by
  unfold diskQuadraticResonance
  with_reducible
    exact EulerNonuniqueness.General.quadratic_resonance_commutator_zero (Space := DiskLinearState)
      diskLinearGroupOperator diskLinearGenerator diskLinearGroupOperator_zero diskLinearGroupOperator_add
      diskLinearGroupOperator_generator diskLinearGroupOperator_period bilinear

theorem diskQuadraticHomologicalSolution_norm_le (bilinear : EulerNonuniqueness.General.BilinearEnd DiskLinearState) :
    ‖diskQuadraticHomologicalSolution bilinear‖ ≤ 2 * Real.pi * diskLinearGroupBound ^ 3 * ‖bilinear‖ := by
  have estimate : ‖diskQuadraticHomologicalSolution bilinear‖ ≤
      (4 * Real.pi / 2) * diskLinearGroupBound ^ 3 * ‖bilinear‖ := by
    unfold diskQuadraticHomologicalSolution
    with_reducible
      exact EulerNonuniqueness.General.quadraticHomologicalSolution_norm_le (Space := DiskLinearState)
        diskLinearGroupOperator diskLinearGenerator (by positivity : 0 < 4 * Real.pi)
        diskLinearGroupBound_nonnegative diskLinearGroupOperator_zero diskLinearGroupOperator_add
        diskLinearGroupOperator_generator diskLinearGroupOperator_norm_bound bilinear
  convert estimate using 1 <;> ring

end

end EulerNonuniqueness.Paper
