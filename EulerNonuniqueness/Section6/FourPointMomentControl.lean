import EulerNonuniqueness.Section6.UniformPointShapeForcing

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace EulerNonuniqueness.Section6

theorem fourPointSignedMoment_norm_le (positions : FourPointConfiguration) :
    ‖fourPointSignedMoment positions‖ ≤ 4 * ‖positions‖ := by
  calc
    _ ≤ ∑ target : Fin 4, ‖(fourPointSign target : ℂ) * positions target‖ := norm_sum_le _ _
    _ ≤ ∑ _target : Fin 4, ‖positions‖ := by
      apply Finset.sum_le_sum
      intro target _
      have signNorm : ‖(fourPointSign target : ℂ)‖ = 1 := by
        by_cases positive : target.val < 2 <;> simp [fourPointSign, positive]
      rw [norm_mul, signNorm, one_mul]
      exact norm_le_pi_norm positions target
    _ = _ := by simp

theorem fourPointSignedMoment_continuous : Continuous fourPointSignedMoment := by
  unfold fourPointSignedMoment
  fun_prop

theorem fourPointSignedMoment_forced_integral {trajectory forcing : ℝ → FourPointConfiguration}
    {coefficient firstTime secondTime : ℝ}
    (forcingContinuous : ContinuousOn forcing (uIcc firstTime secondTime))
    (equation : ∀ time ∈ uIcc firstTime secondTime, ∀ target,
      HasDerivAt (fun current => trajectory current target)
        (fourPointField coefficient (trajectory time) target + forcing time target) time) :
    fourPointSignedMoment (trajectory secondTime) = fourPointSignedMoment (trajectory firstTime) +
      ∫ time in firstTime..secondTime, fourPointSignedMoment (forcing time) := by
  have integrable : IntervalIntegrable (fun time => fourPointSignedMoment (forcing time)) volume firstTime secondTime :=
    (fourPointSignedMoment_continuous.comp_continuousOn forcingContinuous).intervalIntegrable
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time member => fourPointSignedMoment_forced_hasDerivAt (equation time member)) integrable
  linear_combination -identity

theorem fourPointSignedMoment_forced_norm_bound {trajectory forcing : ℝ → FourPointConfiguration}
    {coefficient firstTime secondTime bound : ℝ}
    (forcingContinuous : ContinuousOn forcing (uIcc firstTime secondTime))
    (forcingBound : ∀ time ∈ uIcc firstTime secondTime, ‖forcing time‖ ≤ bound)
    (equation : ∀ time ∈ uIcc firstTime secondTime, ∀ target,
      HasDerivAt (fun current => trajectory current target)
        (fourPointField coefficient (trajectory time) target + forcing time target) time) :
    ‖fourPointSignedMoment (trajectory secondTime)‖ ≤
      ‖fourPointSignedMoment (trajectory firstTime)‖ + 4 * bound * |secondTime - firstTime| := by
  rw [fourPointSignedMoment_forced_integral forcingContinuous equation]
  apply (norm_add_le _ _).trans
  apply add_le_add_left
  have integralControl := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := firstTime) (b := secondTime)
    (f := fun time => fourPointSignedMoment (forcing time)) (C := 4 * bound) (by
      intro time member
      exact (fourPointSignedMoment_norm_le (forcing time)).trans
        (mul_le_mul_of_nonneg_left (forcingBound time (uIoc_subset_uIcc member)) (by norm_num)))
  simpa only [mul_comm] using integralControl

end EulerNonuniqueness.Section6
