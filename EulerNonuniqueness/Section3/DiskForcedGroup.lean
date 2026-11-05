import EulerNonuniqueness.Section3.DiskGroupOperators
import EulerNonuniqueness.General.LinearGroupDuhamel

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance forcedGroupHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance forcedGroupC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance forcedGroupC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance forcedGroupC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance forcedGroupC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance forcedGroupC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance forcedGroupC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance forcedGroupStateBoundedSMul : IsBoundedSMul ℝ DiskLinearState :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := DiskLinearState)
local instance forcedGroupOperatorTopology : TopologicalSpace (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := DiskLinearState) (F := DiskLinearState)
local instance forcedGroupOperatorNormedGroup : NormedAddCommGroup (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)
local instance forcedGroupOperatorSpace : NormedSpace ℝ (DiskLinearState →L[ℝ] DiskLinearState) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := DiskLinearState) (F := DiskLinearState) (σ₁₂ := RingHom.id ℝ)

def diskLinearRateGroup (frequency time : ℝ) : DiskLinearState →L[ℝ] DiskLinearState :=
  diskLinearGroupOperator (frequency * time)

theorem diskLinearRateGroup_zero (frequency : ℝ) :
    diskLinearRateGroup frequency 0 = ContinuousLinearMap.id ℝ DiskLinearState := by
  simpa only [diskLinearRateGroup, mul_zero] using diskLinearGroupOperator_zero

theorem diskLinearRateGroup_add (frequency first second : ℝ) :
    diskLinearRateGroup frequency (first + second) =
      (diskLinearRateGroup frequency first).comp (diskLinearRateGroup frequency second) := by
  simpa only [diskLinearRateGroup, mul_add] using
    diskLinearGroupOperator_add (frequency * first) (frequency * second)

theorem diskLinearRateGroup_hasDerivAt (frequency time : ℝ) :
    HasDerivAt (F := DiskLinearState →L[ℝ] DiskLinearState) (diskLinearRateGroup frequency)
      ((diskLinearRateGroup frequency time).comp (frequency • diskLinearGenerator)) time := by
  have inner : HasDerivAt (fun current : ℝ => frequency * current) frequency time := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id time).const_mul frequency
  have actual := HasDerivAt.scomp (F := DiskLinearState →L[ℝ] DiskLinearState)
    time (diskLinearGroupOperator_generator (frequency * time)) inner
  simpa only [diskLinearRateGroup, ContinuousLinearMap.comp_smul] using actual

theorem diskLinearRateGroup_norm_bound (frequency time : ℝ) (data : DiskLinearState) :
    ‖diskLinearRateGroup frequency time data‖ ≤ diskLinearGroupBound * ‖data‖ :=
  diskLinearGroupOperator_norm_bound (frequency * time) data

theorem diskLinearRateGroup_duhamel
    {trajectory forcing : ℝ → DiskLinearState} {horizon time : ℝ} (frequency : ℝ)
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (equation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt (F := DiskLinearState) trajectory ((frequency • diskLinearGenerator) (trajectory current) + forcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    trajectory time = diskLinearRateGroup frequency time (trajectory 0) +
      ∫ current in (0 : ℝ)..time, diskLinearRateGroup frequency (time - current) (forcing current) := by
  with_reducible
    exact EulerNonuniqueness.General.linearGroup_duhamel (Space := DiskLinearState)
      (trajectory := trajectory) (forcing := forcing) (horizon := horizon) (time := time)
      (diskLinearRateGroup frequency) (frequency • diskLinearGenerator)
      (diskLinearRateGroup_zero frequency) (diskLinearRateGroup_add frequency)
      (diskLinearRateGroup_hasDerivAt frequency) trajectoryContinuous forcingContinuous equation inside

theorem diskLinearRateGroup_response_bound
    {trajectory forcing : ℝ → DiskLinearState} {horizon time : ℝ} (frequency : ℝ)
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (equation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt (F := DiskLinearState) trajectory ((frequency • diskLinearGenerator) (trajectory current) + forcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    ‖trajectory time‖ ≤ diskLinearGroupBound *
      (‖trajectory 0‖ + ∫ current in (0 : ℝ)..time, ‖forcing current‖) := by
  with_reducible
    exact EulerNonuniqueness.General.linearGroup_response_bound (Space := DiskLinearState)
      (trajectory := trajectory) (forcing := forcing) (horizon := horizon) (time := time)
      (diskLinearRateGroup frequency) (frequency • diskLinearGenerator)
      (diskLinearRateGroup_zero frequency) (diskLinearRateGroup_add frequency)
      (diskLinearRateGroup_hasDerivAt frequency) diskLinearGroupBound_nonnegative
      (diskLinearRateGroup_norm_bound frequency) trajectoryContinuous forcingContinuous equation inside

end

end EulerNonuniqueness.Paper
