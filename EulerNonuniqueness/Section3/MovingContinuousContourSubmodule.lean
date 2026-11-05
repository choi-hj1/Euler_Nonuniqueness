import EulerNonuniqueness.Section3.ContourContinuousGauge
import EulerNonuniqueness.Section3.MovingCentroidGaugeShapeEquation
import EulerNonuniqueness.Section3.MovingContourStateProjections
import EulerNonuniqueness.General.ODEClosedSubspaceInvariance

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingContinuousC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance movingContinuousHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingContinuousC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def movingContinuousContourSubmodule (count : ℕ) : Submodule ℝ (MovingContourState count) where
  carrier := {state | ∀ index, state.2.2 index ∈ contourContinuousVectorSubmodule}
  zero_mem' := fun _ => contourContinuousVectorSubmodule.zero_mem
  add_mem' := fun first second index => contourContinuousVectorSubmodule.add_mem (first index) (second index)
  smul_mem' := fun scalar state member index => contourContinuousVectorSubmodule.smul_mem scalar (member index)

theorem movingContinuousContourSubmodule_closed (count : ℕ) :
    IsClosed (movingContinuousContourSubmodule count : Set (MovingContourState count)) := by
  have identity : (movingContinuousContourSubmodule count : Set (MovingContourState count)) =
      ⋂ index : Fin count, {state | state.2.2 index ∈ contourContinuousVectorSubmodule} := by
    ext state
    change (∀ index, state.2.2 index ∈ contourContinuousVectorSubmodule) ↔ _
    simp only [mem_setOf_eq, mem_iInter]
  rw [identity]
  apply isClosed_iInter
  intro index
  exact contourContinuousVectorSubmodule_closed.preimage (movingContourStateShapeCLM count index).continuous

theorem movingCircleInitial_mem_continuousSubmodule {count : ℕ} (clock : ℝ) (centers : Fin count → ℂ) :
    (clock, centers, fun _ : Fin count => standardCircleBanach) ∈ movingContinuousContourSubmodule count :=
  fun _ => standardCircle_mem_contourContinuousVectorSubmodule

theorem FiniteContourConfiguration.movingStateRawField_mem_continuousSubmodule_of_external {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count)
    (members : state ∈ movingContinuousContourSubmodule count)
    (small : ∀ index, ‖state.2.2 index - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (external : ∀ index, configuration.movingStateExternalField state index ∈ contourContinuousVectorSubmodule)
    (index : Fin count) : configuration.movingStateRawField state index ∈ contourContinuousVectorSubmodule := by
  rw [configuration.movingStateRawField_self_external]
  exact contourContinuousVectorSubmodule.add_mem
    (contourContinuousVectorSubmodule.smul_mem (configuration.density index)
      (contourContinuousVectorSubmodule_rotating_self (state.2.2 index) (members index) (small index)))
    (external index)

theorem FiniteContourConfiguration.movingStateVectorField_mem_continuousSubmodule_of_external {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count)
    (members : state ∈ movingContinuousContourSubmodule count)
    (small : ∀ index, ‖state.2.2 index - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (external : ∀ index, configuration.movingStateExternalField state index ∈ contourContinuousVectorSubmodule) :
    configuration.movingStateVectorField state ∈ movingContinuousContourSubmodule count := by
  intro index
  exact contourContinuousVectorSubmodule_centroid_projection (state.2.2 index) _
    (configuration.movingStateRawField_mem_continuousSubmodule_of_external state members small external index)

theorem FiniteContourConfiguration.movingStateCutoffField_mem_continuousSubmodule_of_external {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap margin : ℝ}
    (shapeSmall : shapeRadius < min 1 (2 / (3 * Real.pi)))
    (external : ∀ state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap,
      state ∈ movingContinuousContourSubmodule count →
      ∀ index, configuration.movingStateExternalField state index ∈ contourContinuousVectorSubmodule)
    (state : MovingContourState count) (members : state ∈ movingContinuousContourSubmodule count) :
    configuration.movingStateCutoffField centerBound shapeRadius gap margin state ∈ movingContinuousContourSubmodule count := by
  by_cases inside : state ∈ configuration.movingStateAdmissible centerBound shapeRadius gap
  · exact (movingContinuousContourSubmodule count).smul_mem _
      (configuration.movingStateVectorField_mem_continuousSubmodule_of_external state members
        (fun index => (inside.2.1 index).trans_lt shapeSmall) (external state inside members))
  · unfold FiniteContourConfiguration.movingStateCutoffField
    rw [EulerNonuniqueness.General.distanceFieldCutoff_zero_outside _ margin state inside, zero_smul]
    exact (movingContinuousContourSubmodule count).zero_mem

end EulerNonuniqueness.Paper
