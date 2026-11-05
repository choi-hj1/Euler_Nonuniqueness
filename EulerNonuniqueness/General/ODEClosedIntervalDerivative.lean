import EulerNonuniqueness.General.ContinuousODEFamily

noncomputable section

open Set MeasureTheory
open scoped NNReal

theorem hasDerivWithinAt_Icc_of_continuous_interior_derivative
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space] [CompleteSpace space]
    {trajectory derivative : ℝ → space} {horizon : ℝ}
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (derivativeContinuous : Continuous derivative)
    (interiorDerivative : ∀ time ∈ Ioo 0 horizon, HasDerivAt trajectory (derivative time) time) :
    ∀ time ∈ Icc 0 horizon, HasDerivWithinAt trajectory (derivative time) (Icc 0 horizon) time := by
  let primitive := fun time => trajectory 0 + ∫ current in (0 : ℝ)..time, derivative current
  have primitiveDerivative (time : ℝ) : HasDerivAt primitive (derivative time) time :=
    (intervalIntegral.integral_hasDerivAt_right (derivativeContinuous.intervalIntegrable 0 time)
      derivativeContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      derivativeContinuous.continuousAt).const_add _
  have identity (time : ℝ) (inside : time ∈ Icc 0 horizon) : trajectory time = primitive time := by
    have integralIdentity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1
      (trajectoryContinuous.mono (Icc_subset_Icc le_rfl inside.2))
      (fun current member => interiorDerivative current ⟨member.1, member.2.trans_le inside.2⟩)
      (derivativeContinuous.intervalIntegrable 0 time)
    dsimp only [primitive]
    rw [integralIdentity]
    abel
  intro time inside
  exact (primitiveDerivative time).hasDerivWithinAt.congr identity (identity time inside)

theorem exists_jointly_continuous_family_of_bounded_lipschitz_ODE_with_closed_derivatives
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space] [CompleteSpace space]
    {field : space → space} {lipschitzBound speedBound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound field) (bounded : ∀ state, ‖field state‖ ≤ speedBound)
    {horizon : ℝ} (horizonNonnegative : 0 ≤ horizon) :
    ∃ flow : space → ℝ → space,
      (∀ initial, flow initial 0 = initial) ∧
      Continuous (fun point : space × ℝ => flow point.1 point.2) ∧
      (∀ initial time, time ∈ Icc 0 horizon →
        HasDerivWithinAt (flow initial) (field (flow initial time)) (Icc 0 horizon) time) ∧
      ∀ first second time, dist (flow first time) (flow second time) ≤
        dist first second * Real.exp ((lipschitzBound : ℝ) * horizon) := by
  obtain ⟨flow, initial, jointContinuous, derivatives, stability⟩ :=
    exists_jointly_continuous_family_of_bounded_lipschitz_ODE lipschitz bounded horizonNonnegative
  refine ⟨flow, initial, jointContinuous, ?_, stability⟩
  intro initialPoint
  have trajectoryContinuous : Continuous (flow initialPoint) :=
    jointContinuous.comp (continuous_const.prodMk continuous_id)
  exact hasDerivWithinAt_Icc_of_continuous_interior_derivative trajectoryContinuous.continuousOn
    (lipschitz.continuous.comp trajectoryContinuous) (derivatives initialPoint)
