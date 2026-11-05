import EulerNonuniqueness.Section3.MovingContinuousContourSubmodule
import EulerNonuniqueness.Section3.CrossContourContinuousVectorExtension

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingContinuousFieldC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance movingContinuousFieldC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem contourContinuousVectorSubmodule_complex_smul (scalar : ℂ) (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    scalar • data ∈ contourContinuousVectorSubmodule := by
  have identity : scalar • data = c1Product (c1Constant scalar) data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl
  rw [identity]
  exact contourContinuousVectorSubmodule_constant_product scalar data member

theorem contourContinuousVectorSubmodule_affine (center : ℂ) (radius : ℝ) (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    c1AffineContour center radius data ∈ contourContinuousVectorSubmodule :=
  contourContinuousVectorSubmodule.add_mem (contourContinuousVectorSubmodule_constant center)
    (contourContinuousVectorSubmodule.smul_mem radius member)

theorem FiniteContourConfiguration.movingStatePhysicalContour_mem_continuousSubmodule {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count)
    (members : state ∈ movingContinuousContourSubmodule count) (index : Fin count) :
    configuration.movingStatePhysicalContour state index ∈ contourContinuousVectorSubmodule :=
  contourContinuousVectorSubmodule_affine _ _ _
    (contourContinuousVectorSubmodule_complex_smul _ _ (members index))

theorem FiniteContourConfiguration.movingStateExternalField_mem_continuousSubmodule {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count)
    (members : state ∈ movingContinuousContourSubmodule count) (index : Fin count) :
    configuration.movingStateExternalField state index ∈ contourContinuousVectorSubmodule := by
  unfold FiniteContourConfiguration.movingStateExternalField
  apply Submodule.sum_mem
  intro other otherMember
  apply contourContinuousVectorSubmodule.smul_mem
  apply contourContinuousVectorSubmodule_complex_smul
  exact extendedCrossContourVelocity_mem_of_target _ _
    (configuration.movingStatePhysicalContour_mem_continuousSubmodule state members index)

theorem FiniteContourConfiguration.movingStateCutoffField_mem_continuousSubmodule {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap margin : ℝ}
    (shapeSmall : shapeRadius < min 1 (2 / (3 * Real.pi)))
    (state : MovingContourState count) (members : state ∈ movingContinuousContourSubmodule count) :
    configuration.movingStateCutoffField centerBound shapeRadius gap margin state ∈ movingContinuousContourSubmodule count :=
  configuration.movingStateCutoffField_mem_continuousSubmodule_of_external shapeSmall
    (fun current _ currentMembers =>
      configuration.movingStateExternalField_mem_continuousSubmodule current currentMembers) state members

end EulerNonuniqueness.Paper
