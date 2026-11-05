import EulerNonuniqueness.Section8.AnalyticTimeConcatenation

noncomputable section

open MeasureTheory Set Filter

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.global_timeConcatenation_weakTransport
    {join : ℝ} {initial terminal : Vorticity} {earlier later : Evolution}
    (earlierHypotheses : TransportAnalyticHypotheses join initial earlier)
    (laterHypotheses : ∀ horizon, 0 < horizon → TransportAnalyticHypotheses horizon terminal later)
    (positive : 0 < join) (trace : earlier join =ᵐ[volume] terminal) :
    WeakTransport initial (timeConcatenation join earlier later)
      (fun time => biotSavart (timeConcatenation join earlier later time)) := by
  intro horizon horizonPositive
  by_cases ordered : horizon ≤ join
  · apply (earlierHypotheses.weakTransport.mono ordered).congr_ae
    · have timeInside : ∀ᵐ point : ℝ × Plane ∂spacetimeMeasure horizon, point.1 ∈ Ioo 0 horizon :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
      filter_upwards [timeInside] with point inside
      simp only [Function.uncurry, timeConcatenation, if_pos (inside.2.le.trans ordered)]
    · intro time inside
      simp only [timeConcatenation, if_pos (inside.2.le.trans ordered)]
  · have remainingPositive : 0 < horizon - join := by linarith
    have identity := earlierHypotheses.timeConcatenation_weakTransport
      (laterHypotheses (horizon - join) remainingPositive) positive remainingPositive trace
    simpa only [add_sub_cancel] using identity

end EulerNonuniqueness
