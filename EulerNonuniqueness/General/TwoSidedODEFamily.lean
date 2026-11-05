import EulerNonuniqueness.General.ODEClosedIntervalDerivative

noncomputable section

open Set
open scoped NNReal

theorem exists_jointly_continuous_two_sided_family_of_bounded_lipschitz_ODE
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space] [CompleteSpace space]
    {field : space → space} {lipschitzBound speedBound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound field)
    (bounded : ∀ state, ‖field state‖ ≤ speedBound)
    {backwardHorizon forwardHorizon : ℝ}
    (backwardPositive : 0 < backwardHorizon) (forwardPositive : 0 < forwardHorizon) :
    ∃ flow : space → ℝ → space,
      (∀ initial, flow initial 0 = initial) ∧
      Continuous (fun point : space × ℝ => flow point.1 point.2) ∧
      (∀ initial time, time ∈ Ioo (-backwardHorizon) forwardHorizon →
        HasDerivAt (flow initial) (field (flow initial time)) time) := by
  obtain ⟨forward, forwardInitial, forwardContinuous, forwardDerivative, _⟩ :=
    exists_jointly_continuous_family_of_bounded_lipschitz_ODE_with_closed_derivatives
      lipschitz bounded forwardPositive.le
  obtain ⟨backward, backwardInitial, backwardContinuous, backwardDerivative, _⟩ :=
    exists_jointly_continuous_family_of_bounded_lipschitz_ODE_with_closed_derivatives
      lipschitz.neg (fun state => by simpa using bounded state) backwardPositive.le
  let flow := fun initial time => if 0 ≤ time then forward initial time else backward initial (-time)
  have initialIdentity (initial : space) : flow initial 0 = initial := by
    simp [flow, forwardInitial]
  have jointContinuous : Continuous (fun point : space × ℝ => flow point.1 point.2) := by
    apply forwardContinuous.if_le
      (backwardContinuous.comp (continuous_fst.prodMk continuous_snd.neg))
      continuous_const continuous_snd
    intro point equality
    have timeZero : point.2 = 0 := equality.symm
    simp [timeZero, forwardInitial, backwardInitial]
  refine ⟨flow, initialIdentity, jointContinuous, ?_⟩
  intro initial time inside
  rcases inside with ⟨afterBackward, beforeForward⟩
  have forwardAgreement : EqOn (flow initial) (forward initial) (Ici 0) := by
    intro current member
    simp [flow, show 0 ≤ current from member]
  have backwardAgreement : EqOn (flow initial) (fun current => backward initial (-current)) (Iic 0) := by
    intro current member
    by_cases zero : current = 0
    · simp [zero, flow, forwardInitial, backwardInitial]
    · simp [flow, show ¬0 ≤ current from fun nonnegative => zero (le_antisymm member nonnegative)]
  rcases lt_trichotomy time 0 with negative | zero | positive
  · have derivative := (backwardDerivative initial (-time) ⟨by linarith, by linarith⟩).hasDerivAt
      (Icc_mem_nhds (by linarith) (by linarith))
    have composed := derivative.scomp time (hasDerivAt_id time).neg
    have agreement : flow initial =ᶠ[nhds time] fun current => backward initial (-current) :=
      Filter.eventually_of_mem (Iic_mem_nhds negative) backwardAgreement
    simpa [Function.comp_def, flow, not_le.mpr negative] using
      composed.congr_of_eventuallyEq agreement
  · subst time
    have right := (forwardDerivative initial 0 ⟨le_rfl, forwardPositive.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨le_rfl, forwardPositive⟩)
    have rightFlow := right.congr forwardAgreement (forwardAgreement (mem_Ici.mpr le_rfl))
    have leftRaw := (backwardDerivative initial 0 ⟨le_rfl, backwardPositive.le⟩).scomp_of_eq 0
      ((hasDerivAt_id (0 : ℝ)).neg.hasDerivWithinAt (s := Icc (-backwardHorizon) 0))
      (fun current member => by change 0 ≤ -current ∧ -current ≤ backwardHorizon; constructor <;> linarith [member.1, member.2]) (neg_zero.symm)
    have left := leftRaw.mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem ⟨by linarith, le_rfl⟩)
    have leftFlow := left.congr backwardAgreement (backwardAgreement (mem_Iic.mpr le_rfl))
    have rightFinal : HasDerivWithinAt (flow initial) (field (flow initial 0)) (Ici 0) 0 := by
      simpa [initialIdentity, forwardInitial] using rightFlow
    have leftFinal : HasDerivWithinAt (flow initial) (field (flow initial 0)) (Iic 0) 0 := by
      simpa [initialIdentity, backwardInitial, neg_smul] using leftFlow
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using leftFinal.union rightFinal
  · have derivative := (forwardDerivative initial time ⟨positive.le, beforeForward.le⟩).hasDerivAt
      (Icc_mem_nhds positive beforeForward)
    have agreement : flow initial =ᶠ[nhds time] forward initial :=
      Filter.eventually_of_mem (Ici_mem_nhds positive) forwardAgreement
    simpa [flow, positive.le] using derivative.congr_of_eventuallyEq agreement

theorem exists_jointly_continuous_clamped_two_sided_family_of_bounded_lipschitz_ODE
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space] [CompleteSpace space]
    {field : space → space} {lipschitzBound speedBound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound field)
    (bounded : ∀ state, ‖field state‖ ≤ speedBound)
    {backwardHorizon forwardHorizon : ℝ}
    (backwardPositive : 0 < backwardHorizon) (forwardPositive : 0 < forwardHorizon) :
    ∃ flow : space → ℝ → space,
      (∀ initial, flow initial 0 = initial) ∧
      Continuous (fun point : space × ℝ => flow point.1 point.2) ∧
      (∀ initial time, time ∈ Ioo (-backwardHorizon) forwardHorizon →
        HasDerivAt (flow initial) (field (flow initial time)) time) ∧
      ∀ initial time, ∃ clampedTime ∈ Icc (-backwardHorizon) forwardHorizon,
        flow initial time = flow initial clampedTime := by
  obtain ⟨original, initialIdentity, jointContinuous, derivatives⟩ :=
    exists_jointly_continuous_two_sided_family_of_bounded_lipschitz_ODE
      lipschitz bounded backwardPositive forwardPositive
  have ordered : -backwardHorizon ≤ forwardHorizon := by linarith
  let projection : ℝ → Icc (-backwardHorizon) forwardHorizon :=
    projIcc (-backwardHorizon) forwardHorizon ordered
  have projectionIdentity (time : ℝ) (inside : time ∈ Icc (-backwardHorizon) forwardHorizon) :
      (projection time : ℝ) = time :=
    congrArg Subtype.val (projIcc_of_mem ordered inside)
  let flow := fun initial time => original initial (projection time)
  have agrees (initial : space) (time : ℝ) (inside : time ∈ Icc (-backwardHorizon) forwardHorizon) :
      flow initial time = original initial time := by
    dsimp only [flow]
    rw [projectionIdentity time inside]
  refine ⟨flow, ?_, ?_, ?_, ?_⟩
  · intro initial
    rw [agrees initial 0 ⟨by linarith, forwardPositive.le⟩, initialIdentity]
  · have projectionContinuous : Continuous projection := continuous_projIcc
    exact jointContinuous.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp projectionContinuous).comp continuous_snd))
  · intro initial time inside
    have eventuallyAgrees : flow initial =ᶠ[nhds time] original initial :=
      Filter.eventually_of_mem (Icc_mem_nhds inside.1 inside.2) (agrees initial)
    rw [agrees initial time ⟨inside.1.le, inside.2.le⟩]
    exact (derivatives initial time inside).congr_of_eventuallyEq eventuallyAgrees
  · intro initial time
    refine ⟨projection time, (projection time).property, ?_⟩
    rw [agrees initial (projection time) (projection time).property]
