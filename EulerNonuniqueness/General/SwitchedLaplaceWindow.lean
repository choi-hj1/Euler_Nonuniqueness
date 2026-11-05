import EulerNonuniqueness.General.AffineLaplaceWindow

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace intervalIntegral

private theorem incoming_laplace_prefix_le {amplitude rate weight entry finish : ℝ}
    (amplitudeNonnegative : 0 ≤ amplitude) (weightPositive : 0 < weight)
    (rateBound : 2 * weight ≤ rate) (finishBound : finish ≤ entry) :
    (∫ time in (0 : ℝ)..finish,
      Real.exp (-weight * time) * (amplitude * Real.exp (rate * (time - entry)))) ≤
      (2 * amplitude / rate) * Real.exp (-weight * entry) := by
  have ratePositive : 0 < rate := by linarith only [weightPositive, rateBound]
  have gapPositive : 0 < rate - weight := by linarith only [weightPositive, rateBound]
  have identity (time : ℝ) : Real.exp (-weight * time) * (amplitude * Real.exp (rate * (time - entry))) =
      (amplitude * Real.exp (-rate * entry)) * Real.exp ((rate - weight) * time) := by
    rw [mul_left_comm, ← Real.exp_add]
    have exponent : -weight * time + rate * (time - entry) = -rate * entry + (rate - weight) * time := by ring
    rw [exponent, Real.exp_add]
    ring
  have integralIdentity :
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (amplitude * Real.exp (rate * (time - entry)))) =
        (amplitude * Real.exp (-rate * entry)) *
          (Real.exp ((rate - weight) * finish) - 1) / (rate - weight) := by
    simp_rw [identity]
    rw [integral_const_mul, integral_comp_mul_left Real.exp gapPositive.ne', integral_exp]
    simp only [mul_zero, Real.exp_zero, smul_eq_mul]
    ring
  have exponential : Real.exp (-rate * entry) * Real.exp ((rate - weight) * finish) ≤ Real.exp (-weight * entry) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left finishBound gapPositive.le]
  have coefficient : amplitude / (rate - weight) ≤ 2 * amplitude / rate := by
    apply (div_le_div_iff₀ gapPositive ratePositive).mpr
    nlinarith only [mul_nonneg amplitudeNonnegative (show 0 ≤ rate - 2 * weight by linarith only [rateBound])]
  rw [integralIdentity]
  calc
    _ ≤ amplitude * Real.exp (-rate * entry) * Real.exp ((rate - weight) * finish) / (rate - weight) := by
      have discarded := mul_nonneg amplitudeNonnegative (Real.exp_pos (-rate * entry)).le
      apply div_le_div_of_nonneg_right _ gapPositive.le
      nlinarith only [discarded]
    _ = (amplitude / (rate - weight)) *
        (Real.exp (-rate * entry) * Real.exp ((rate - weight) * finish)) := by ring
    _ ≤ (amplitude / (rate - weight)) * Real.exp (-weight * entry) :=
      mul_le_mul_of_nonneg_left exponential (div_nonneg amplitudeNonnegative gapPositive.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right coefficient (Real.exp_pos _).le

private theorem switched_source_laplace_le {amplitude rate slope constant weight entry finish : ℝ}
    (amplitudeNonnegative : 0 ≤ amplitude) (slopeNonnegative : 0 ≤ slope) (constantNonnegative : 0 ≤ constant)
    (entryNonnegative : 0 ≤ entry) (finishNonnegative : 0 ≤ finish)
    (weightPositive : 0 < weight) (rateBound : 2 * weight ≤ rate) :
    let source := fun time => if time ≤ entry then
      Real.exp (-weight * time) * (amplitude * Real.exp (rate * (time - entry)))
      else Real.exp (-weight * time) * (slope * (time - entry) + constant)
    IntervalIntegrable source volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, source time) ≤
      (2 * amplitude / rate) * Real.exp (-weight * entry) +
        if entry < finish then (slope / weight ^ 2 + constant / weight) * Real.exp (-weight * entry) else 0 := by
  classical
  intro source
  let incoming := fun time => Real.exp (-weight * time) * (amplitude * Real.exp (rate * (time - entry)))
  let outgoing := fun time => Real.exp (-weight * time) * (slope * (time - entry) + constant)
  have incomingContinuous : Continuous incoming := by fun_prop
  have outgoingContinuous : Continuous outgoing := by fun_prop
  have incomingI := incomingContinuous.intervalIntegrable (μ := volume) 0 finish
  have outgoingI := outgoingContinuous.intervalIntegrable (μ := volume) 0 finish
  have piecewiseI : Integrable ((Iic entry).piecewise incoming outgoing) (volume.restrict (uIoc 0 finish)) :=
    Integrable.piecewise measurableSet_Iic incomingI.def'.integrable.integrableOn outgoingI.def'.integrable.integrableOn
  have sourceI : IntervalIntegrable source volume 0 finish := by
    apply intervalIntegrable_iff.mpr
    simpa only [source, incoming, outgoing, Set.piecewise, mem_Iic] using piecewiseI
  refine ⟨sourceI, ?_⟩
  by_cases active : entry < finish
  · have entryInside : entry ∈ uIcc (0 : ℝ) finish := by
      rw [uIcc_of_le finishNonnegative]
      exact ⟨entryNonnegative, active.le⟩
    have parts := (IntervalIntegrable.trans_iff entryInside).mp sourceI
    have leftIdentity : (∫ time in (0 : ℝ)..entry, source time) = ∫ time in (0 : ℝ)..entry, incoming time := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun time inside => by
        rw [uIoc_of_le entryNonnegative] at inside
        simp only [source, inside.2, ite_true, incoming])
    have rightIdentity : (∫ time in entry..finish, source time) = ∫ time in entry..finish, outgoing time := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun time inside => by
        rw [uIoc_of_le active.le] at inside
        simp only [source, not_le.mpr inside.1, ite_false, outgoing])
    have affine := integral_exp_neg_mul_le_of_affine_majorant
      (function := fun time => slope * (time - entry) + constant) (weight := weight)
      (slope := slope) (constant := constant) (origin := entry) (start := entry) (finish := finish)
      (by fun_prop) weightPositive slopeNonnegative constantNonnegative le_rfl active.le (fun _ _ => le_rfl)
    have outgoingIdentity : (∫ time in entry..finish, outgoing time) = Real.exp (-weight * entry) *
        ∫ time in entry..finish, Real.exp (-weight * (time - entry)) * (slope * (time - entry) + constant) := by
      rw [← integral_const_mul]
      apply integral_congr
      intro time _
      dsimp only [outgoing]
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring
    have outgoingBound : (∫ time in entry..finish, outgoing time) ≤
        (slope / weight ^ 2 + constant / weight) * Real.exp (-weight * entry) := by
      rw [outgoingIdentity]
      simpa only [sub_self, mul_zero, zero_add, mul_comm] using
        mul_le_mul_of_nonneg_left affine.2 (Real.exp_pos (-weight * entry)).le
    rw [if_pos active, ← integral_add_adjacent_intervals parts.1 parts.2, leftIdentity, rightIdentity]
    exact add_le_add (incoming_laplace_prefix_le amplitudeNonnegative weightPositive rateBound le_rfl) outgoingBound
  · have bound : finish ≤ entry := le_of_not_gt active
    have identity : (∫ time in (0 : ℝ)..finish, source time) = ∫ time in (0 : ℝ)..finish, incoming time := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun time inside => by
        rw [uIoc_of_le finishNonnegative] at inside
        simp only [source, inside.2.trans bound, ite_true, incoming])
    rw [if_neg active, add_zero, identity]
    exact incoming_laplace_prefix_le amplitudeNonnegative weightPositive rateBound bound

theorem integral_exp_neg_mul_le_of_finite_switched_majorant {ι : Type*}
    (sources : Finset ι) {function feedback : ℝ → ℝ}
    (entry amplitude rate slope constant : ι → ℝ) {weight tolerance finish : ℝ}
    (functionContinuous : ContinuousOn function (Icc 0 finish))
    (feedbackContinuous : ContinuousOn feedback (Icc 0 finish))
    (finishNonnegative : 0 ≤ finish) (weightPositive : 0 < weight) (_toleranceNonnegative : 0 ≤ tolerance)
    (sourceBounds : ∀ source ∈ sources, 0 ≤ entry source ∧ 0 ≤ amplitude source ∧
      0 ≤ slope source ∧ 0 ≤ constant source ∧ 2 * weight ≤ rate source)
    (majorized : ∀ time ∈ Icc 0 finish, function time ≤
      (∑ source ∈ sources, if time ≤ entry source then amplitude source * Real.exp (rate source * (time - entry source))
        else slope source * (time - entry source) + constant source) + tolerance * feedback time) :
    IntervalIntegrable (fun time => Real.exp (-weight * time) * function time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * feedback time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time) ≤
      (∑ source ∈ sources, (2 * amplitude source / rate source) * Real.exp (-weight * entry source)) +
      (∑ source ∈ sources.filter (fun source => entry source < finish),
        (slope source / weight ^ 2 + constant source / weight) * Real.exp (-weight * entry source)) +
      tolerance * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * feedback time := by
  classical
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have functionI := (exponentialContinuous.continuousOn.mul functionContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have feedbackI := (exponentialContinuous.continuousOn.mul feedbackContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  let source := fun index time => if time ≤ entry index then
    Real.exp (-weight * time) * (amplitude index * Real.exp (rate index * (time - entry index)))
    else Real.exp (-weight * time) * (slope index * (time - entry index) + constant index)
  have action (index : ι) (member : index ∈ sources) :=
    switched_source_laplace_le (sourceBounds index member).2.1 (sourceBounds index member).2.2.1
      (sourceBounds index member).2.2.2.1 (sourceBounds index member).1 finishNonnegative weightPositive
      (sourceBounds index member).2.2.2.2
  have sourceI : IntervalIntegrable (fun time => ∑ index ∈ sources, source index time) volume 0 finish := by
    have integrable := IntervalIntegrable.sum (s := sources) (f := source) (fun index member => (action index member).1)
    convert integrable using 1
    funext time
    simp only [Finset.sum_apply]
  have weightedMajorized (time : ℝ) (inside : time ∈ Icc 0 finish) :
      Real.exp (-weight * time) * function time ≤
        (∑ index ∈ sources, source index time) + tolerance * (Real.exp (-weight * time) * feedback time) := by
    have scaled := mul_le_mul_of_nonneg_left (majorized time inside) (Real.exp_pos (-weight * time)).le
    convert scaled using 1
    rw [mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro index _
      dsimp only [source]
      split_ifs <;> rfl
    · ring
  have integrated := integral_mono_on finishNonnegative functionI (sourceI.add (feedbackI.const_mul tolerance)) weightedMajorized
  rw [integral_add sourceI (feedbackI.const_mul tolerance), integral_const_mul,
    integral_finset_sum (fun index member => (action index member).1)] at integrated
  have sumBound := Finset.sum_le_sum (fun index member => (action index member).2)
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero] at sumBound
  refine ⟨functionI, feedbackI, integrated.trans (add_le_add_right sumBound _)⟩

end intervalIntegral
