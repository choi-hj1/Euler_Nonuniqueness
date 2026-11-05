import EulerNonuniqueness.General.LinearGroupDuhamel
import EulerNonuniqueness.General.ClosedIntervalODEExtension

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem linearGroup_pair_history_of_interior
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first final : ℝ, group (first + final) = (group first).comp (group final))
    (groupDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    {bound : ℝ} (boundNonnegative : 0 ≤ bound)
    (groupBound : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ bound * ‖value‖)
    {firstCurve finalCurve firstForcing finalForcing : ℝ → Space} {horizon : ℝ}
    (horizonNonnegative : 0 ≤ horizon)
    (firstContinuous : ContinuousOn firstCurve (Icc 0 horizon))
    (finalContinuous : ContinuousOn finalCurve (Icc 0 horizon))
    (firstForcingContinuous : ContinuousOn firstForcing (Icc 0 horizon))
    (finalForcingContinuous : ContinuousOn finalForcing (Icc 0 horizon))
    (firstEquation : ∀ time ∈ Ioo 0 horizon,
      HasDerivAt firstCurve (generator (firstCurve time) + firstForcing time) time)
    (finalEquation : ∀ time ∈ Ioo 0 horizon,
      HasDerivAt finalCurve (generator (finalCurve time) + finalForcing time) time) :
    ∀ time ∈ Icc 0 horizon,
      finalCurve time - firstCurve time = group time (finalCurve 0 - firstCurve 0) +
        ∫ current in (0 : ℝ)..time, group (time - current) (finalForcing current - firstForcing current) ∧
      ‖finalCurve time - firstCurve time‖ ≤ bound *
        (‖finalCurve 0 - firstCurve 0‖ + ∫ current in (0 : ℝ)..time, ‖finalForcing current - firstForcing current‖) := by
  let trajectory := fun time => finalCurve time - firstCurve time
  let forcing := fun time => finalForcing time - firstForcing time
  let velocity := fun time => generator (trajectory time) + forcing time
  have trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon) := finalContinuous.sub firstContinuous
  have forcingContinuous : ContinuousOn forcing (Icc 0 horizon) := finalForcingContinuous.sub firstForcingContinuous
  have velocityContinuous : ContinuousOn velocity (Icc 0 horizon) :=
    (generator.continuous.comp_continuousOn trajectoryContinuous).add forcingContinuous
  have equation (time : ℝ) (inside : time ∈ Ioo 0 horizon) : HasDerivAt trajectory (velocity time) time := by
    have actual := (finalEquation time inside).sub (firstEquation time inside)
    have identity : (generator (finalCurve time) + finalForcing time) -
        (generator (firstCurve time) + firstForcing time) = velocity time := by
      simp only [velocity, trajectory, forcing, map_sub]
      abel
    exact actual.congr_deriv identity
  obtain ⟨extended, extendedContinuous, agreement, extendedEquation⟩ :=
    exists_closedInterval_ode_extension horizonNonnegative trajectoryContinuous velocityContinuous equation
  have closedEquation (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      HasDerivAt extended (generator (extended time) + forcing time) time := by
    have actual := extendedEquation time inside
    simpa only [velocity, agreement inside] using actual
  intro time inside
  have exactHistory := linearGroup_duhamel group generator atZero addition groupDerivative
    extendedContinuous.continuousOn forcingContinuous closedEquation inside
  have normHistory := linearGroup_response_bound group generator atZero addition groupDerivative
    boundNonnegative groupBound extendedContinuous.continuousOn forcingContinuous closedEquation inside
  rw [agreement inside, agreement ⟨le_rfl, horizonNonnegative⟩] at exactHistory normHistory
  exact ⟨exactHistory, normHistory⟩

end EulerNonuniqueness.General
