import EulerNonuniqueness.Section8.TransportTestCoefficient
import EulerNonuniqueness.Section8.TimeL2Products
import EulerNonuniqueness.Section8.Globalization

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.integrable_transport_test
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point : ℝ × Plane => omega point.1 point.2 *
      transportTestCoefficient test omega point) (spacetimeMeasure horizon) := by
  obtain ⟨sourceBound, sourceFinite, sourceBounded⟩ := hypotheses.uniformBounds 2 (by norm_num)
  obtain ⟨coefficientBound, coefficientNonnegative, coefficientMeasurable, coefficientIntegrable, coefficientProperties⟩ :=
    hypotheses.transport_test_coefficient_properties nonnegative smooth compact
  have timeInside : ∀ᵐ time ∂volume.restrict (Ioo 0 horizon), time ∈ Ioo 0 horizon :=
    ae_restrict_mem measurableSet_Ioo
  apply integrable_prod_mul_of_uniform_L2
    (firstBound := sourceBound.toReal) (secondBound := coefficientBound)
    hypotheses.weakTransport.aestronglyMeasurable coefficientMeasurable
  · exact timeInside.mono fun time inside => hypotheses.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩
  · exact timeInside.mono fun time inside => (coefficientProperties time ⟨inside.1.le, inside.2.le⟩).1
  · filter_upwards [timeInside] with time inside
    exact ENNReal.toReal_mono sourceFinite.ne
      (by simpa using sourceBounded time ⟨inside.1.le, inside.2.le⟩)
  · exact timeInside.mono fun time inside => (coefficientProperties time ⟨inside.1.le, inside.2.le⟩).2
  · exact ENNReal.toReal_nonneg

end EulerNonuniqueness
