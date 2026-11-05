import EulerNonuniqueness.General.ODEClosedIntervalDerivative

noncomputable section

open Set

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem trajectory_mem_closed_submodule_of_bounded_lipschitz_field
    (subspace : Submodule ℝ Space) (closed : IsClosed (subspace : Set Space))
    {field : Space → Space} {constant speed : NNReal}
    (lipschitz : LipschitzWith constant field) (bounded : ∀ state, ‖field state‖ ≤ speed)
    (preserves : ∀ state ∈ subspace, field state ∈ subspace)
    {trajectory : ℝ → Space} {horizon : ℝ} (horizonNonnegative : 0 ≤ horizon)
    (continuous : ContinuousOn trajectory (Icc 0 horizon))
    (equation : ∀ time ∈ Icc 0 horizon,
      HasDerivWithinAt trajectory (field (trajectory time)) (Icc 0 horizon) time)
    (initial : trajectory 0 ∈ subspace) :
    ∀ time ∈ Icc 0 horizon, trajectory time ∈ subspace := by
  letI : CompleteSpace subspace := closed.completeSpace_coe
  let restricted : subspace → subspace := fun state => ⟨field state.val, preserves state.val state.property⟩
  have restrictedLipschitz : LipschitzWith constant restricted := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    exact lipschitz.dist_le_mul first.val second.val
  have restrictedBound : ∀ state, ‖restricted state‖ ≤ speed := fun state => bounded state.val
  obtain ⟨flow, initialIdentity, jointContinuous, derivatives, _stability⟩ :=
    exists_jointly_continuous_family_of_bounded_lipschitz_ODE_with_closed_derivatives
      restrictedLipschitz restrictedBound horizonNonnegative
  let initialState : subspace := ⟨trajectory 0, initial⟩
  let comparison : ℝ → Space := fun time => (flow initialState time).val
  have comparisonContinuous : Continuous comparison :=
    continuous_subtype_val.comp (jointContinuous.comp (continuous_const.prodMk continuous_id))
  have comparisonEquation (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      HasDerivWithinAt comparison (field (comparison time)) (Icc 0 horizon) time := by
    have actual := HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ) (F := subspace) (E := Space) time
      subspace.subtypeL.hasFDerivAt (derivatives initialState time inside)
    exact actual
  have equal : EqOn trajectory comparison (Icc 0 horizon) := by
    apply ODE_solution_unique (v := fun _ => field) (K := constant)
      (fun _ => lipschitz) continuous
    · intro time inside
      exact (equation time ⟨inside.1, inside.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem inside)
    · exact comparisonContinuous.continuousOn
    · intro time inside
      exact (comparisonEquation time ⟨inside.1, inside.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem inside)
    · change trajectory 0 = (flow initialState 0).val
      rw [initialIdentity]
  intro time inside
  rw [equal inside]
  exact (flow initialState time).property

end EulerNonuniqueness.General
