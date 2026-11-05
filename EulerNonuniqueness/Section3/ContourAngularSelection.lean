import EulerNonuniqueness.Section3.ContourContinuousFourierAverage
import EulerNonuniqueness.Section3.AngularOperatorAverage

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance angularSelectionC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

local instance angularSelectionPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem contourContinuousVector_of_labelShift (data : PeriodicC1HolderHalf)
    (orbit : Continuous (fun offset => contourLabelShiftCCLM offset data)) :
    data ∈ contourContinuousVectorSubmodule := by
  have circleContinuous : Continuous standardCircle := by unfold standardCircle; fun_prop
  have relation (offset : ℝ) : normalizedContourShiftCLM offset data =
      star (standardCircle offset) • contourLabelShiftCCLM offset data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [complexC1Holder_smul_value, contourLabelShiftCCLM_value, standardCircle_star_eq_inv]
    rfl
  change Continuous (fun offset => normalizedContourShiftCLM offset data)
  simpa only [relation] using circleContinuous.star.smul orbit

theorem contourC1FourierAverage_operator (operator : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf)
    (shift : ℤ) (equivariant : ∀ offset current, contourLabelShiftCCLM offset (operator current) =
      circleFourierReal (-shift) offset • operator (contourLabelShiftCCLM offset current))
    (data : PeriodicC1HolderHalf) (member : data ∈ contourContinuousVectorSubmodule) (degree : ℤ) :
    contourC1FourierAverage (operator data) degree =
      operator (contourC1FourierAverage data (degree + shift)) := by
  have result := angularOperatorAverage_intertwines contourLabelShiftCCLM operator shift equivariant data
    (continuous_contourLabelShiftCCLM data member) degree
  simpa only [angularOperatorAverage, contourC1FourierAverage] using result

theorem contourAngularOperator_fourier_zero (operator : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf)
    (shift : ℤ) (equivariant : ∀ offset current, contourLabelShiftCCLM offset (operator current) =
      circleFourierReal (-shift) offset • operator (contourLabelShiftCCLM offset current))
    (data : PeriodicC1HolderHalf) (member : data ∈ contourContinuousVectorSubmodule) (degree : ℤ)
    (inputZero : fourierCoeff (periodicContinuousLift data.val.1.continuous
      (PeriodicC1HolderHalf.periodic data)) (degree + shift) = 0) :
    fourierCoeff (periodicContinuousLift (operator data).val.1.continuous
      (PeriodicC1HolderHalf.periodic (operator data))) degree = 0 := by
  have outputOrbit : Continuous (fun offset => contourLabelShiftCCLM offset (operator data)) := by
    with_reducible
      exact continuous_orbit_of_angular_intertwining contourLabelShiftCCLM operator shift equivariant data
        (continuous_contourLabelShiftCCLM data member)
  have outputMember := contourContinuousVector_of_labelShift (operator data) outputOrbit
  apply (contourC1FourierAverage_eq_zero_iff (operator data) outputMember degree).mp
  rw [contourC1FourierAverage_operator operator shift equivariant data member degree,
    (contourC1FourierAverage_eq_zero_iff data member (degree + shift)).mpr inputZero, map_zero]

theorem contourAngularOperator_shift_two_negative_zero
    (operator : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf)
    (equivariant : ∀ offset current, contourLabelShiftCCLM offset (operator current) =
      circleFourierReal (-2) offset • operator (contourLabelShiftCCLM offset current))
    (data : PeriodicC1HolderHalf) (member : data ∈ contourContinuousVectorSubmodule)
    (positiveInput : ∀ degree : ℤ, degree ≤ 1 →
      fourierCoeff (periodicContinuousLift data.val.1.continuous (PeriodicC1HolderHalf.periodic data)) degree = 0)
    (degree : ℤ) (negative : degree ≤ -2) :
    fourierCoeff (periodicContinuousLift (operator data).val.1.continuous
      (PeriodicC1HolderHalf.periodic (operator data))) degree = 0 := by
  exact contourAngularOperator_fourier_zero operator 2 equivariant data member degree
    (positiveInput (degree + 2) (by omega))

end

end EulerNonuniqueness.Paper
