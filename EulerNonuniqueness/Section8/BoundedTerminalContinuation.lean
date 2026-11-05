import EulerNonuniqueness.Section8.AnalyticConcatenationData
import EulerNonuniqueness.Section8.BoundedDatumGlobalSupport
import EulerNonuniqueness.Section8.EulerSolutionRestriction

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.exists_global_continuation
    {join : ℝ} {initial : Vorticity} {earlier : Evolution}
    (analytic : TransportAnalyticHypotheses join initial earlier) (positive : 0 < join)
    (terminalMeasurable : Measurable (earlier join))
    {terminalBound : ℝ} (boundNonnegative : 0 ≤ terminalBound)
    (terminalBounded : ∀ position, ‖earlier join position‖ ≤ terminalBound)
    {radius : ℝ} (radiusPositive : 0 < radius)
    (supported : ∀ time ∈ Icc 0 join, support (earlier time) ⊆ Metric.closedBall 0 radius) :
    ∃ omega : Evolution, IsEulerSolution initial omega ∧
      (∀ time : ℝ, time ≤ join → omega time = earlier time) ∧
      (∀ time : ℝ, 0 ≤ time → support (omega time) ⊆
        Metric.closedBall 0 (radius + regularizedSourceSpeed (earlier join) * time)) ∧
      ∀ time : ℝ, 0 ≤ time → InitialDatum (omega time) := by
  have terminalInside : join ∈ Icc 0 join := ⟨positive.le, le_rfl⟩
  have terminalDatum : InitialDatum (earlier join) :=
    ⟨HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 radius) (supported join terminalInside),
      fun exponent exponentBound => analytic.membership exponent exponentBound join terminalInside,
      analytic.zeroMean join terminalInside⟩
  obtain ⟨later, laterSolution, _, laterSupport, laterDatum⟩ :=
    exists_growing_support_global_eulerSolution_of_bounded_initialDatum terminalDatum terminalMeasurable
      boundNonnegative terminalBounded radiusPositive (supported join terminalInside)
  have speedNonnegative := regularizedSourceSpeed_nonnegative (earlier join)
  have laterAnalytic (horizon : ℝ) (horizonPositive : 0 < horizon) :
      TransportAnalyticHypotheses horizon (earlier join) later := by
    apply (laterSolution.on_interval horizonPositive).transportAnalyticHypotheses terminalDatum
    · refine ⟨radius + regularizedSourceSpeed (earlier join) * horizon, by positivity, ?_⟩
      intro time inside
      exact (laterSupport time inside.1).trans (Metric.closedBall_subset_closedBall
        (add_le_add_left (mul_le_mul_of_nonneg_left inside.2 speedNonnegative) radius))
    · intro time inside
      exact (laterDatum time inside.1).2.2
  let omega := EulerNonuniqueness.timeConcatenation join earlier later
  have solution : IsEulerSolution initial omega := analytic.global_timeConcatenation_solution
    laterAnalytic positive Filter.EventuallyEq.rfl
  have retained (time : ℝ) (before : time ≤ join) : omega time = earlier time :=
    if_pos before
  have growingSupport (time : ℝ) (nonnegative : 0 ≤ time) :
      support (omega time) ⊆ Metric.closedBall 0 (radius + regularizedSourceSpeed (earlier join) * time) := by
    by_cases before : time ≤ join
    · rw [retained time before]
      exact (supported time ⟨nonnegative, before⟩).trans (Metric.closedBall_subset_closedBall
        (le_add_of_nonneg_right (mul_nonneg speedNonnegative nonnegative)))
    · have shiftedNonnegative : 0 ≤ time - join := by linarith
      change support (if time ≤ join then earlier time else later (time - join)) ⊆ _
      rw [if_neg before]
      exact (laterSupport (time - join) shiftedNonnegative).trans (Metric.closedBall_subset_closedBall
        (add_le_add_left (mul_le_mul_of_nonneg_left (by linarith : time - join ≤ time) speedNonnegative) radius))
  refine ⟨omega, solution, retained, growingSupport, ?_⟩
  intro time nonnegative
  by_cases before : time ≤ join
  · rw [retained time before]
    exact ⟨HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 radius)
      (supported time ⟨nonnegative, before⟩),
      fun exponent exponentBound => analytic.membership exponent exponentBound time ⟨nonnegative, before⟩,
      analytic.zeroMean time ⟨nonnegative, before⟩⟩
  · have shiftedNonnegative : 0 ≤ time - join := by linarith
    simpa only [omega, EulerNonuniqueness.timeConcatenation, if_neg before] using laterDatum (time - join) shiftedNonnegative

end EulerNonuniqueness
