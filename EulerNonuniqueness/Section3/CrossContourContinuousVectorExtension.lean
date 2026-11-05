import EulerNonuniqueness.Section3.CrossContourContinuousVectors

noncomputable section

namespace EulerNonuniqueness.Paper

local instance crossExtensionContinuousVectorC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace

theorem extendedCrossContourVelocity_mem_of_target (target source : PeriodicC1HolderHalf)
    (member : target ∈ contourContinuousVectorSubmodule) :
    extendedCrossContourVelocity target source ∈ contourContinuousVectorSubmodule := by
  by_cases separated : UniformlySeparatedContours target source
  · exact extendedCrossContourVelocity_mem_contourContinuousVectorSubmodule target source member separated
  · rw [extendedCrossContourVelocity, dif_neg separated]
    exact contourContinuousVectorSubmodule.zero_mem

end EulerNonuniqueness.Paper
