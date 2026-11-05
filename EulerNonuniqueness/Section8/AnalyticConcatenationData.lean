import EulerNonuniqueness.Section8.AnalyticTimeConcatenation
import EulerNonuniqueness.Section8.GlobalLpTimeConcatenation
import EulerNonuniqueness.Section8.MomentEulerLimit
import EulerNonuniqueness.Section8.TransportAnalyticDecay

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.timeConcatenation
    {first second : ℝ} {initial terminal : Vorticity} {earlier later : Evolution}
    (earlierHypotheses : TransportAnalyticHypotheses first initial earlier)
    (laterHypotheses : TransportAnalyticHypotheses second terminal later)
    (firstPositive : 0 < first) (secondPositive : 0 < second)
    (trace : earlier first =ᵐ[volume] terminal) :
    TransportAnalyticHypotheses (first + second) initial (EulerNonuniqueness.timeConcatenation first earlier later) := by
  have endpoint : earlier first =ᵐ[volume] later 0 :=
    trace.trans (laterHypotheses.initial_ae_eq secondPositive).symm
  have twoEarlier : ContinuousInLpOn first 2 earlier := by
    simpa using earlierHypotheses.continuousInLp_vorticity firstPositive (exponent := 2) (by norm_num)
  have twoLater : ContinuousInLpOn second 2 later := by
    simpa using laterHypotheses.continuousInLp_vorticity secondPositive (exponent := 2) (by norm_num)
  obtain ⟨earlierRadius, earlierRadiusPositive, earlierSupport⟩ := earlierHypotheses.supported
  obtain ⟨laterRadius, laterRadiusPositive, laterSupport⟩ := laterHypotheses.supported
  refine ⟨earlierHypotheses.timeConcatenation_weakTransport laterHypotheses firstPositive secondPositive trace,
    twoEarlier.timeConcatenation_weakL2ContinuousOn twoLater firstPositive.le secondPositive.le endpoint,
    ⟨max earlierRadius laterRadius, lt_max_of_lt_left earlierRadiusPositive, ?_⟩, ?_, ?_, ?_⟩
  · intro time inside
    by_cases before : time ≤ first
    · simpa only [EulerNonuniqueness.timeConcatenation, if_pos before] using
        (earlierSupport time ⟨inside.1, before⟩).trans
          (Metric.closedBall_subset_closedBall (le_max_left earlierRadius laterRadius))
    · have shiftedInside : time - first ∈ Icc 0 second := by constructor <;> linarith [inside.2]
      simpa only [EulerNonuniqueness.timeConcatenation, if_neg before] using
        (laterSupport (time - first) shiftedInside).trans
          (Metric.closedBall_subset_closedBall (le_max_right earlierRadius laterRadius))
  · intro exponent exponentBound time inside
    by_cases before : time ≤ first
    · simpa only [EulerNonuniqueness.timeConcatenation, if_pos before] using
        earlierHypotheses.membership exponent exponentBound time ⟨inside.1, before⟩
    · have shiftedInside : time - first ∈ Icc 0 second := by constructor <;> linarith [inside.2]
      simpa only [EulerNonuniqueness.timeConcatenation, if_neg before] using
        laterHypotheses.membership exponent exponentBound (time - first) shiftedInside
  · intro exponent exponentBound
    obtain ⟨earlierBound, earlierFinite, earlierBounded⟩ := earlierHypotheses.uniformBounds exponent exponentBound
    obtain ⟨laterBound, laterFinite, laterBounded⟩ := laterHypotheses.uniformBounds exponent exponentBound
    refine ⟨max earlierBound laterBound, max_lt earlierFinite laterFinite, ?_⟩
    intro time inside
    by_cases before : time ≤ first
    · simpa only [EulerNonuniqueness.timeConcatenation, if_pos before] using
        (earlierBounded time ⟨inside.1, before⟩).trans (le_max_left earlierBound laterBound)
    · have shiftedInside : time - first ∈ Icc 0 second := by constructor <;> linarith [inside.2]
      simpa only [EulerNonuniqueness.timeConcatenation, if_neg before] using
        (laterBounded (time - first) shiftedInside).trans (le_max_right earlierBound laterBound)
  · intro time inside
    by_cases before : time ≤ first
    · simpa only [EulerNonuniqueness.timeConcatenation, if_pos before] using
        earlierHypotheses.zeroMean time ⟨inside.1, before⟩
    · have shiftedInside : time - first ∈ Icc 0 second := by constructor <;> linarith [inside.2]
      simpa only [EulerNonuniqueness.timeConcatenation, if_neg before] using
        laterHypotheses.zeroMean (time - first) shiftedInside

theorem TransportAnalyticHypotheses.global_timeConcatenation_solution
    {join : ℝ} {initial terminal : Vorticity} {earlier later : Evolution}
    (earlierHypotheses : TransportAnalyticHypotheses join initial earlier)
    (laterHypotheses : ∀ horizon : ℝ, 0 < horizon → TransportAnalyticHypotheses horizon terminal later)
    (positive : 0 < join) (trace : earlier join =ᵐ[volume] terminal) :
    IsEulerSolution initial (EulerNonuniqueness.timeConcatenation join earlier later) := by
  apply isEulerSolution_of_isEulerSolutionOn
  intro horizon horizonPositive
  have analytic := earlierHypotheses.timeConcatenation (laterHypotheses horizon horizonPositive)
    positive horizonPositive trace
  exact (analytic.isEulerSolutionOn (add_pos positive horizonPositive) analytic.continuousInLp_biotSavart).mono
    (le_add_of_nonneg_left positive.le)

end EulerNonuniqueness
