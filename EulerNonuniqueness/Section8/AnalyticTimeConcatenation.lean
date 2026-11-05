import EulerNonuniqueness.Section8.TimeConcatenation
import EulerNonuniqueness.Section8.AnalyticTerminalTrace

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.timeConcatenation_weakTransport
    {first second : ℝ} {initial terminal : Vorticity} {earlier later : Evolution}
    (earlierHypotheses : TransportAnalyticHypotheses first initial earlier)
    (laterHypotheses : TransportAnalyticHypotheses second terminal later)
    (firstPositive : 0 < first) (secondPositive : 0 < second)
    (trace : earlier first =ᵐ[volume] terminal) :
    WeakTransportOn (first + second) initial (timeConcatenation first earlier later)
      (fun time => biotSavart (timeConcatenation first earlier later time)) := by
  have identity := earlierHypotheses.weakTransport.timeConcatenation firstPositive secondPositive
    laterHypotheses.weakTransport trace
    (fun _ smooth compact => earlierHypotheses.integrable_transport_test firstPositive.le smooth compact)
    (fun _ smooth compact => by
      apply ContinuousInLpOn.continuousOn_moving_test_moment _ smooth compact
      simpa using earlierHypotheses.continuousInLp_vorticity firstPositive (exponent := 1) le_rfl)
  have velocityEquality : timeConcatenation first
      (fun time => biotSavart (earlier time)) (fun time => biotSavart (later time)) =
        (fun time => biotSavart (timeConcatenation first earlier later time)) := by
    funext time
    by_cases inside : time ≤ first <;> simp [timeConcatenation, inside]
  rw [velocityEquality] at identity
  exact identity

end EulerNonuniqueness
