import EulerNonuniqueness.General.LinearExponentialGroup

namespace EulerNonuniqueness.General

noncomputable section

open MeasureTheory

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem linearGroup_fixed_of_generator_zero
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (actualDerivative : ∀ time, HasDerivAt group ((group time).comp generator) time)
    {value : Space} (kernel : generator value = 0) (time : ℝ) : group time value = value := by
  have derivative (current : ℝ) : HasDerivAt (fun parameter => group parameter value) 0 current := by
    simpa only [ContinuousLinearMap.comp_apply, kernel, map_zero, add_zero] using
      (actualDerivative current).clm_apply (hasDerivAt_const current value)
  have actual := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun current _ => derivative current)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : Space)) volume 0 time)
  simpa only [intervalIntegral.integral_zero, atZero, ContinuousLinearMap.id_apply, sub_eq_zero] using actual.symm

theorem linearExponentialGroup_fixed_of_generator_zero
    (operator : Space →L[ℝ] Space) {value : Space} (kernel : operator value = 0) (time : ℝ) :
    linearExponentialGroup operator time value = value :=
  linearGroup_fixed_of_generator_zero (linearExponentialGroup operator) operator
    (linearExponentialGroup_zero operator) (linearExponentialGroup_hasDerivAt_right operator) kernel time

end

end EulerNonuniqueness.General
