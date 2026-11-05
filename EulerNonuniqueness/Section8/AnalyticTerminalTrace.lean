import EulerNonuniqueness.Section8.AnalyticTransportIntegrability
import EulerNonuniqueness.Section8.AllLpVorticityContinuity
import EulerNonuniqueness.Section8.MovingTestMoment
import EulerNonuniqueness.Section8.TerminalTransportTrace

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.terminal_test_identity
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun position => initial position * test (0, position)) ∧
      (∫ point : ℝ × Plane, omega point.1 point.2 *
        (timeDerivative test point + spatialDerivative test point (biotSavart (omega point.1) point.2))
          ∂spacetimeMeasure horizon) + (∫ position, initial position * test (0, position)) =
            ∫ position, omega horizon position * test (horizon, position) := by
  apply hypotheses.weakTransport.terminal_test_identity positive smooth compact
  · exact hypotheses.integrable_transport_test positive.le smooth compact
  · apply ContinuousInLpOn.continuousOn_moving_test_moment (test := test) _ smooth compact
    simpa using hypotheses.continuousInLp_vorticity positive (exponent := 1) le_rfl

end EulerNonuniqueness
