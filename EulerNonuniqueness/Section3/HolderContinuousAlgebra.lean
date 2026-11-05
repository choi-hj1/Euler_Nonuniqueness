import EulerNonuniqueness.Section3.HolderContinuousVectors
import EulerNonuniqueness.General.ContinuousVectorBilinear
import EulerNonuniqueness.Section3.HolderDifferentialAlgebra
import EulerNonuniqueness.Section3.CircleRadialCauchy

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] holderContinuousRealSpace

theorem holderContinuousVectorSubmodule_product (first second : PeriodicHolderHalf)
    (firstMember : first ∈ holderContinuousVectorSubmodule) (secondMember : second ∈ holderContinuousVectorSubmodule) :
    holderProduct first second ∈ holderContinuousVectorSubmodule := by
  apply EulerNonuniqueness.General.continuousVectorSubmodule_bilinear holderPureLabelAction holderProductRealCLM
    (fun time left right => ?_) first second firstMember secondMember
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

theorem holderContinuousVectorSubmodule_conjugate (data : PeriodicHolderHalf)
    (member : data ∈ holderContinuousVectorSubmodule) : holderConjugate data ∈ holderContinuousVectorSubmodule := by
  have orbit : Continuous (fun time => holderConjugateCLM (holderPureLabelAction time data)) :=
    holderConjugateCLM.continuous.comp member
  have identity : (fun time => holderConjugateCLM (holderPureLabelAction time data)) =
      fun time => holderPureLabelAction time (holderConjugate data) := by
    funext time
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  rw [identity] at orbit
  exact orbit

theorem holderRealPart_coe_re_value (data : PeriodicHolderHalf) (label : ℝ) :
    (holderRealPart data).val.1 label = ((data.val.1 label).re : ℂ) := by
  change (1 / 2 : ℝ) • (data.val.1 label + star (data.val.1 label)) = _
  rw [Complex.real_smul]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem holderContinuousVectorSubmodule_realPart (data : PeriodicHolderHalf)
    (member : data ∈ holderContinuousVectorSubmodule) : holderRealPart data ∈ holderContinuousVectorSubmodule :=
  holderContinuousVectorSubmodule.smul_mem _
    (holderContinuousVectorSubmodule.add_mem member (holderContinuousVectorSubmodule_conjugate data member))

theorem holderContinuousVectorSubmodule_inverse (data : PeriodicHolderHalf)
    (member : data ∈ holderContinuousVectorSubmodule) {lower : ℝ} (positive : 0 < lower)
    (separated : ∀ label, lower ≤ ‖data.val.1 label‖) : extendedHolderInverse data ∈ holderContinuousVectorSubmodule := by
  have shiftedLower (time label : ℝ) : lower ≤ ‖(holderPureLabelAction time data).val.1 label‖ :=
    separated (label + time)
  have orbitSource : Continuous (fun current => holderPureLabelAction current data) := member
  have orbit : Continuous (fun time => extendedHolderInverse (holderPureLabelAction time data)) := by
    apply continuous_iff_continuousAt.mpr
    intro time
    exact ContinuousAt.comp (f := fun current : ℝ => holderPureLabelAction current data)
      (g := extendedHolderInverse) (x := time)
      (hasFDerivAt_extendedHolderInverse (holderPureLabelAction time data) positive (shiftedLower time)).continuousAt
      (orbitSource.continuousAt (x := time))
  have identity : (fun time => extendedHolderInverse (holderPureLabelAction time data)) =
      fun time => holderPureLabelAction time (extendedHolderInverse data) := by
    funext time
    rw [extendedHolderInverse_eq (holderPureLabelAction time data) positive (shiftedLower time),
      extendedHolderInverse_eq data positive separated]
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  rw [identity] at orbit
  exact orbit

end EulerNonuniqueness.Paper
