import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem linearGroup_duhamel
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (groupDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    {trajectory forcing : ℝ → Space} {horizon time : ℝ}
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (equation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt trajectory (generator (trajectory current) + forcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    trajectory time = group time (trajectory 0) +
      ∫ current in (0 : ℝ)..time, group (time - current) (forcing current) := by
  have groupContinuous : Continuous group :=
    continuous_iff_continuousAt.mpr (fun current => (groupDerivative current).continuousAt)
  have groupApply (first second : ℝ) (value : Space) :
      group first (group second value) = group (first + second) value :=
    (congrArg (fun operator : Space →L[ℝ] Space => operator value) (addition first second)).symm
  have inverseDerivative (current : ℝ) : HasDerivAt (fun position => group (-position))
      (-((group (-current)).comp generator)) current := by
    have inner : HasDerivAt (fun position : ℝ => -position) (-1) current := by
      simpa only [id_eq] using (hasDerivAt_id current).neg
    simpa only [neg_one_smul] using (groupDerivative (-current)).scomp current inner
  have transformedDerivative (current : ℝ) (currentInside : current ∈ Icc 0 horizon) :
      HasDerivAt (fun position => group (-position) (trajectory position))
        (group (-current) (forcing current)) current := by
    have actual := (inverseDerivative current).clm_apply (equation current currentInside)
    convert actual using 1
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, map_add]
    abel
  have subset : Icc 0 time ⊆ Icc 0 horizon := fun _ membership =>
    ⟨membership.1, membership.2.trans inside.2⟩
  have kernelContinuous : ContinuousOn (fun current => group (-current) (forcing current)) (Icc 0 time) :=
    ((groupContinuous.comp continuous_neg).continuousOn).clm_apply (forcingContinuous.mono subset)
  have kernelIntegrable := kernelContinuous.intervalIntegrable_of_Icc (μ := volume) inside.1
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun current currentInside => transformedDerivative current (subset (by
      simpa only [uIcc_of_le inside.1] using currentInside))) kernelIntegrable
  change (∫ current in (0 : ℝ)..time, group (-current) (forcing current)) =
    group (-time) (trajectory time) - group (-0) (trajectory 0) at fundamental
  rw [neg_zero, atZero, ContinuousLinearMap.id_apply] at fundamental
  have transformed : group (-time) (trajectory time) = trajectory 0 +
      ∫ current in (0 : ℝ)..time, group (-current) (forcing current) := by
    rw [fundamental]
    abel
  have mapped := congrArg (group time) transformed
  rw [groupApply, add_neg_cancel, atZero, ContinuousLinearMap.id_apply, map_add,
    ← (group time).intervalIntegral_comp_comm kernelIntegrable] at mapped
  simp_rw [groupApply, ← sub_eq_add_neg] at mapped
  exact mapped

theorem linearGroup_response_bound
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (groupDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    {bound : ℝ} (boundNonnegative : 0 ≤ bound)
    (groupBound : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ bound * ‖value‖)
    {trajectory forcing : ℝ → Space} {horizon time : ℝ}
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (equation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt trajectory (generator (trajectory current) + forcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    ‖trajectory time‖ ≤ bound * (‖trajectory 0‖ + ∫ current in (0 : ℝ)..time, ‖forcing current‖) := by
  have groupContinuous : Continuous group :=
    continuous_iff_continuousAt.mpr (fun current => (groupDerivative current).continuousAt)
  have subset : Icc 0 time ⊆ Icc 0 horizon := fun _ membership =>
    ⟨membership.1, membership.2.trans inside.2⟩
  have kernelContinuous : ContinuousOn (fun current => group (time - current) (forcing current)) (Icc 0 time) :=
    ((groupContinuous.comp (continuous_const.sub continuous_id)).continuousOn).clm_apply
      (forcingContinuous.mono subset)
  have kernelIntegrable := kernelContinuous.intervalIntegrable_of_Icc (μ := volume) inside.1
  have forcingIntegrable := (forcingContinuous.mono subset).norm.intervalIntegrable_of_Icc (μ := volume) inside.1
  rw [linearGroup_duhamel group generator atZero addition groupDerivative trajectoryContinuous
    forcingContinuous equation inside]
  calc
    _ ≤ ‖group time (trajectory 0)‖ +
        ‖∫ current in (0 : ℝ)..time, group (time - current) (forcing current)‖ := norm_add_le _ _
    _ ≤ bound * ‖trajectory 0‖ +
        ∫ current in (0 : ℝ)..time, ‖group (time - current) (forcing current)‖ :=
      add_le_add (groupBound time _) (intervalIntegral.norm_integral_le_integral_norm inside.1)
    _ ≤ bound * ‖trajectory 0‖ +
        ∫ current in (0 : ℝ)..time, bound * ‖forcing current‖ := by
      apply add_le_add_left
      exact intervalIntegral.integral_mono_on inside.1 kernelIntegrable.norm
        (forcingIntegrable.const_mul bound) (fun current _ => groupBound (time - current) (forcing current))
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

end

end EulerNonuniqueness.General
