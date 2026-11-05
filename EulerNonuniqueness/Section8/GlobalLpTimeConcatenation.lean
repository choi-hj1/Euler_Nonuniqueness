import EulerNonuniqueness.Section8.LpTimeConcatenation
import EulerNonuniqueness.Section8.ExpandingEulerSequence

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace EulerNonuniqueness

theorem ContinuousInLpOn.global_timeConcatenation {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [MeasurableSpace Value] [BorelSpace Value]
    {join : ℝ} {exponent : ℝ≥0∞} {earlier later : ℝ → Plane → Value}
    (earlierContinuous : ContinuousInLpOn join exponent earlier)
    (laterContinuous : ∀ horizon, 0 < horizon → ContinuousInLpOn horizon exponent later)
    (positive : 0 < join) (trace : earlier join =ᵐ[volume] later 0) :
    ContinuousInLp exponent (EulerNonuniqueness.timeConcatenation join earlier later) := by
  apply continuousInLp_of_continuousInLpOn
  intro horizon horizonPositive
  by_cases ordered : horizon ≤ join
  · apply (earlierContinuous.mono ordered).congr_ae
    intro time inside
    exact Filter.Eventually.of_forall fun position => by
      simp only [EulerNonuniqueness.timeConcatenation, if_pos (inside.2.trans ordered)]
  · have remainingPositive : 0 < horizon - join := by linarith
    have continuity := earlierContinuous.timeConcatenation
      (laterContinuous (horizon - join) remainingPositive) positive.le remainingPositive.le trace
    simpa only [add_sub_cancel] using continuity

theorem ContinuousInLpOn.timeConcatenation_weakL2ContinuousOn
    {first second : ℝ} {earlier later : Evolution}
    (earlierContinuous : ContinuousInLpOn first 2 earlier)
    (laterContinuous : ContinuousInLpOn second 2 later)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second)
    (trace : earlier first =ᵐ[volume] later 0) :
    WeakL2ContinuousOn (first + second) (EulerNonuniqueness.timeConcatenation first earlier later) :=
  (earlierContinuous.timeConcatenation laterContinuous firstNonnegative secondNonnegative trace).weakL2ContinuousOn

end EulerNonuniqueness
