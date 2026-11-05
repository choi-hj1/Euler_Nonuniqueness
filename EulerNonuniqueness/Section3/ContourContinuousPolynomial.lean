import EulerNonuniqueness.Section3.ContourContinuousComposition
import EulerNonuniqueness.Section3.ContourContinuousGauge
import EulerNonuniqueness.Section3.RelabeledDiskForcingPrimitive

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] continuousFourierC1Group holderContinuousRealSpace
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourContinuousPolynomial_product (first second : PeriodicC1HolderHalf)
    (firstMember : first ∈ contourContinuousVectorSubmodule)
    (secondMember : second ∈ contourContinuousVectorSubmodule) :
    c1Product first second ∈ contourContinuousVectorSubmodule := by
  apply contourContinuousVector_of_tangent
  have firstTerm := holderContinuousVectorSubmodule_product first.val.2 (c1ValueHolder second)
    (contourContinuousVector_tangent first firstMember) (c1ValueHolder_mem_holderContinuousVectorSubmodule second)
  have secondTerm := holderContinuousVectorSubmodule_product (c1ValueHolder first) second.val.2
    (c1ValueHolder_mem_holderContinuousVectorSubmodule first) (contourContinuousVector_tangent second secondMember)
  have identity : (c1Product first second).val.2 =
      holderProduct first.val.2 (c1ValueHolder second) + holderProduct (c1ValueHolder first) second.val.2 := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  rw [identity]
  exact holderContinuousVectorSubmodule.add_mem firstTerm secondTerm

theorem contourContinuousPolynomial_conjugate (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    c1Conjugate data ∈ contourContinuousVectorSubmodule := by
  apply contourContinuousVector_of_tangent
  have identity : (c1Conjugate data).val.2 = holderConjugate data.val.2 := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  rw [identity]
  exact holderContinuousVectorSubmodule_conjugate data.val.2 (contourContinuousVector_tangent data member)

theorem contourContinuousPolynomial_complex_smul (coefficient : ℂ) (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    coefficient • data ∈ contourContinuousVectorSubmodule := by
  have identity : coefficient • data = c1Product (c1Constant coefficient) data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl
  rw [identity]
  exact contourContinuousVectorSubmodule_constant_product coefficient data member

theorem contourContinuousVectorSubmodule_naturalPower (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) (degree : ℕ) :
    c1NaturalPower data degree ∈ contourContinuousVectorSubmodule := by
  induction degree with
  | zero => exact contourContinuousVectorSubmodule_constant 1
  | succ degree induction => exact contourContinuousPolynomial_product data _ member induction

theorem contourContinuousVectorSubmodule_tsum {Index : Type*} (term : Index → PeriodicC1HolderHalf)
    (summable : Summable term) (member : ∀ index, term index ∈ contourContinuousVectorSubmodule) :
    (∑' index, term index) ∈ contourContinuousVectorSubmodule := by
  apply contourContinuousVectorSubmodule_closed.mem_of_tendsto summable.hasSum
  exact Filter.Eventually.of_forall (fun selected => contourContinuousVectorSubmodule.sum_mem
    (fun index _ => member index))

end EulerNonuniqueness.Paper
