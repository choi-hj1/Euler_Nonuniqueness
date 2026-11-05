import EulerNonuniqueness.General.CommonLinearPairHistory

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem zeroGenerator_pair_history_of_interior
    {firstCurve finalCurve firstForcing finalForcing : ℝ → Space} {horizon : ℝ}
    (horizonNonnegative : 0 ≤ horizon)
    (firstContinuous : ContinuousOn firstCurve (Icc 0 horizon))
    (finalContinuous : ContinuousOn finalCurve (Icc 0 horizon))
    (firstForcingContinuous : ContinuousOn firstForcing (Icc 0 horizon))
    (finalForcingContinuous : ContinuousOn finalForcing (Icc 0 horizon))
    (firstEquation : ∀ time ∈ Ioo 0 horizon, HasDerivAt firstCurve (firstForcing time) time)
    (finalEquation : ∀ time ∈ Ioo 0 horizon, HasDerivAt finalCurve (finalForcing time) time) :
    ∀ time ∈ Icc 0 horizon,
      finalCurve time - firstCurve time = finalCurve 0 - firstCurve 0 +
        ∫ current in (0 : ℝ)..time, finalForcing current - firstForcing current ∧
      ‖finalCurve time - firstCurve time‖ ≤
        ‖finalCurve 0 - firstCurve 0‖ + ∫ current in (0 : ℝ)..time, ‖finalForcing current - firstForcing current‖ := by
  let group := fun _ : ℝ => ContinuousLinearMap.id ℝ Space
  have addition (first final : ℝ) : group (first + final) = (group first).comp (group final) := by ext value; rfl
  have derivative (time : ℝ) : HasDerivAt group ((group time).comp (0 : Space →L[ℝ] Space)) time := by
    simpa only [group, ContinuousLinearMap.comp_zero] using
      (hasDerivAt_const time (ContinuousLinearMap.id ℝ Space))
  have actual := linearGroup_pair_history_of_interior group 0 rfl addition derivative (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ value => by simp only [group, ContinuousLinearMap.id_apply, one_mul]; exact le_rfl)
    horizonNonnegative firstContinuous finalContinuous firstForcingContinuous finalForcingContinuous
    (fun time inside => by simpa only [ContinuousLinearMap.zero_apply, zero_add] using firstEquation time inside)
    (fun time inside => by simpa only [ContinuousLinearMap.zero_apply, zero_add] using finalEquation time inside)
  simpa only [group, ContinuousLinearMap.id_apply, one_mul] using actual

end EulerNonuniqueness.General
