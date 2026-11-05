import EulerNonuniqueness.Section3.ContourTangentContinuousVectors
import EulerNonuniqueness.Section3.HolderContinuousComposition
import EulerNonuniqueness.Section3.HolderContinuousAlgebra

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] continuousFourierC1Group holderContinuousRealSpace
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

namespace PeriodicC1LabelMap

def slopeHolder (labels : PeriodicC1LabelMap) : PeriodicHolderHalf :=
  PeriodicHolderHalf.ofFunction (fun label => (labels.slope label : ℂ))
    (Complex.continuous_ofReal.comp labels.slope_continuous) labels.bound labels.holder
    (fun label => by simpa only [Complex.norm_real, Real.norm_eq_abs] using labels.slope_bound label)
    (fun first second => by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact labels.holder_bound first second)
    (fun label => congrArg Complex.ofReal (labels.slope_periodic label))

theorem slopeHolder_value (labels : PeriodicC1LabelMap) (label : ℝ) :
    labels.slopeHolder.val.1 label = (labels.slope label : ℂ) := rfl

theorem composeCLM_mem_continuousVector (labels : PeriodicC1LabelMap)
    (slopeMember : labels.slopeHolder ∈ holderContinuousVectorSubmodule)
    (data : PeriodicC1HolderHalf) (member : data ∈ contourContinuousVectorSubmodule) :
    labels.composeCLM data ∈ contourContinuousVectorSubmodule := by
  apply contourContinuousVector_of_tangent
  have tangentMember := contourContinuousVector_tangent data member
  have composedMember := labels.composeHolder_mem_continuousVector data.val.2 tangentMember
  have productMember := holderContinuousVectorSubmodule_product labels.slopeHolder
    (labels.composeHolderCLM data.val.2) slopeMember composedMember
  have identity : (labels.composeCLM data).val.2 =
      holderProduct labels.slopeHolder (labels.composeHolderCLM data.val.2) := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  rw [identity]
  exact productMember

end PeriodicC1LabelMap

end EulerNonuniqueness.Paper
