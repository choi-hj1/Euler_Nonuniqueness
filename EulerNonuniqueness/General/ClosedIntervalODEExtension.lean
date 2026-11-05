import EulerNonuniqueness.General.ODEPrimitiveExtension

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem exists_closedInterval_ode_extension
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    {trajectory velocity : ℝ → Space} {horizon : ℝ}
    (horizonNonnegative : 0 ≤ horizon)
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (velocityContinuous : ContinuousOn velocity (Icc 0 horizon))
    (equation : ∀ time ∈ Ioo 0 horizon, HasDerivAt trajectory (velocity time) time) :
    ∃ extended : ℝ → Space, Continuous extended ∧
      EqOn extended trajectory (Icc 0 horizon) ∧
      ∀ time ∈ Icc 0 horizon, HasDerivAt extended (velocity time) time := by
  let extendedVelocity : ℝ → Space := fun time => velocity (projIcc 0 horizon horizonNonnegative time)
  have continuousVelocity : Continuous extendedVelocity :=
    (continuousOn_iff_continuous_restrict.mp velocityContinuous).comp continuous_projIcc
  have agrees (time : ℝ) (inside : time ∈ Icc 0 horizon) : extendedVelocity time = velocity time := by
    simp only [extendedVelocity, projIcc_of_mem horizonNonnegative inside]
  refine ⟨odePrimitiveExtension trajectory extendedVelocity,
    odePrimitiveExtension_continuous trajectory extendedVelocity continuousVelocity, ?_, ?_⟩
  · intro time inside
    have integralIdentity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1
      (trajectoryContinuous.mono (Icc_subset_Icc le_rfl inside.2))
      (fun current member => by
        rw [agrees current ⟨member.1.le, member.2.le.trans inside.2⟩]
        exact equation current ⟨member.1, member.2.trans_le inside.2⟩)
      (continuousVelocity.intervalIntegrable 0 time)
    rw [odePrimitiveExtension, integralIdentity]
    abel
  · intro time inside
    simpa only [agrees time inside] using
      odePrimitiveExtension_hasDerivAt trajectory extendedVelocity continuousVelocity time

end EulerNonuniqueness.General
